# Rules

A rule name is the label you pass to [`ratchet!`](@ref) and write in opt-out comments. The names
below are conventions; any lowercase words joined by `-` work.

Rules that need the compiler's answer read a loaded module. Rules about how code is written read
source files.

## Rules on a loaded module

These see inferred types, bindings and closures. They need `using MyPackage`. The rules that read
inferred types take their signatures from the caller: `inferred_methods(MyPackage, signatures)` infers the
methods those signatures reach, so the result is the same on every run. The `corset` command line has no signatures, so it skips these two rules.

### `hidden-input`: `hidden_inputs(mod)`

Reads of a non-constant or mutable global, or of a `ScopedValue`. The result of such a function
depends on state its signature does not show.

Repair: pass the value as an argument, or return it from the function that computes it.

### `abstract-local`: `abstract_locals(repo, inferred_methods(mod, signatures))`

Local variables whose inferred type is abstract or a union, one site per variable however many
specializations ran. The usual causes are an accumulator that starts as `0` and receives floats, and
a variable assigned from a container of abstract type.

Repair: initialize with the right type (`zero(eltype(xs))`) or annotate the local.

### `bang`: `unmarked_effects(repo, inferred_methods(mod, signatures))`

Functions that always return `nothing` and have no `!` in the name. A function with a `nothing`
method beside methods that return values (a dispatch on "off") is not reported.

Repair: add the `!`.

### Anonymous functions: `impure-anonymous-function`, `unstable-anonymous-function`, `overspecialized-anonymous-function`

Three rules on anonymous functions (lambdas, `do` blocks and the generators of comprehensions) that
capture variables; Julia calls these closures. One passes all three when it captures nothing
(`x -> x.field`), or when every instance the package compiled captures only plain immutable data:
non-function `isbits` values, `String`s, `Symbol`s, and immutable structs, tuples or small unions of them
(`x -> x * scale` with `scale::Float64`). The rules read the compiled instances from
`Base.specializations`, so they see what the package's precompile workload ran.

| Rule | Function | Finds | Repair |
| --- | --- | --- | --- |
| `impure-anonymous-function` | `impure_anonymous_functions(mod)` | a mutable capture (an array, `Dict`, `Ref`, a module); a `Core.Box`, a captured variable rebound; no compiled instance, so the captures are unverified | pass the data as an argument, or use `Base.Fix1`/`Base.Fix2` (`filter(in(allowed), items)`); cover an unverified function in the precompile workload |
| `unstable-anonymous-function` | `unstable_anonymous_functions(mod)` | a capture whose type inference left abstract, or an instance built where the capture types are unknown | make the captured variable's type concrete, or pass it as an argument |
| `overspecialized-anonymous-function` | `overspecialized_anonymous_functions(mod)` | a captured type or function: the anonymous function compiles anew for every value | pass it as an argument, or define a callable struct whose field is a `DataType` or `Function` |

### `abstract-field`: `abstract_fields(type)`, `repeated-prefix`: `repeated_prefix(type)`

Both take a struct type. Apply them to every struct a module defines with `module_structs(mod)` and
place each site with `struct_site(name, struct_locations(files))`.

- `abstract_fields` finds fields declared with an abstract type, or with a concrete container of one:
  `Vector{Any}`, `Base.RefValue{Any}` and `Dict{Tuple, Any}` are concrete, but every read from them is
  dynamically dispatched. Repair: make the field type a type parameter of the struct.
- `repeated_prefix` finds field names that repeat a word the type should say once. Fields
  `continuation_step` and `continuation_theta` belong in a `ContinuationControls`.

`mutable-struct` reports every struct of `mutable_structs(mod)`. Repair: return the changed data from
the function that computes it and keep the struct immutable. A struct that needs a finalizer, a
cyclic reference or a lock's identity opts out with `# lint: mutable-struct` and a reason.
A limit on field count (`wide-struct`) takes one line: `fieldcount(T) > limit` over
`module_structs(mod)`.

```julia
files = repository_sources(REPO, ("src",))
locations = struct_locations(files)
sites = [struct_site(nameof(T), locations) for T in module_structs(MyPackage) if !isempty(abstract_fields(T))]
ratchet!(REPO, "abstract-field", sites)
```

## Rules on source files

Each takes a file path and `located_source(file)`, the parsed file.

| Rule | Function | Finds | Repair |
| --- | --- | --- | --- |
| `nothing-return` | `nothing_returns` | declared `Union{Nothing, …}` results | return a value that always means something, or throw |
| `range-guard` | `range_guards` | `floatmin`/`floatmax`, `exp`'s range edges (88, 709), `isfinite(exp(…))` | compute in log space or clamp at the source |
| `repeated-statement` | `repeated_statements` | a statement repeated in one block; the same line in two branches passes | delete the copy |
| `return-type` | `return_type_calls` | calls of `Core.Compiler.return_type`, a guess at a result type | restructure so the type is known |
| `concrete-arg` | `concrete_arguments` | arguments annotated `Vector`, `Matrix`, `Array` or `Dict` that the method never resizes | `AbstractVector{T}` and the like; they accept views, `OffsetArray` and GPU arrays |
| `concrete-return` | `concrete_returns(file, located, mod)` | result types that name a concrete type, `Vector{E}` included; `AbstractMatrix{T}` passes; a constructor returning its own type is exempt | annotate by what the arguments bind; `Corset.CONCRETE_RETURN_FIX` is the log text |
| `annotation` | `missing_annotations` | methods with an unannotated argument or result | annotate |
| `float64` | `float64_sites(file)` | `Float64` tokens and untyped float literals | `zero(T)`, `T(0.5)` or `oftype(x, 0.5)` |
| `ref` | `ref_sites(file)` | `Ref` and `RefValue` outside `ccall`, `@ccall`, `cfunction`, `@cfunction` and `@ccallable` | Return the changed data from the function that computes it. A broadcast shield (`f.(Ref(x), xs)`) opts out with `# lint: ref` |
| `c-type` | `c_type_sites(file)` | `Cint`, `Cdouble` and the other C-interop types outside `ccall`, `@ccall`, `cfunction`, `@cfunction` and `@ccallable` | `Int`, `Float64` or `String`; convert at the `ccall` |
| `one-letter` | `one_letter_sites(repo, file)` | one-letter variable names (exempt: `_` and `Repository.one_letter_exempt`) | name the variable |

## Rules with fixers

Two rules come with a function that repairs what they find.

### `misplaced-import`: `misplaced_imports(repo, directories)`

Imports that their file does not use, or that only other files of the module use. An import item
belongs in the files that use its name. `place_imports!(repo, directories)` deletes the unused ones
and moves the rest, and returns the sites it handled.

### `where-return`: `where_return_sites(file)`

Short-form definitions whose `where` binds the return annotation:

```julia
f(x::T)::T where {T} = x      # parses as f(x::T)::(T where {T}); T is not the method's T
(f(x::T)::T) where {T} = x    # what was meant
```

`fix_where_returns!` parenthesizes them.

## Rules that call other tools

### `fatou`: `fatou_sites(repo, directories)`

One site per finding of [Fatou](https://github.com/jolars/fatou)'s `fatou lint`, keyed by file and
Fatou rule. `fatou` must be on `PATH`; the rule errors if it is not.

### `jet`: [`@call_sites`](@ref), [`@opt_sites`](@ref)

Reports of `JET.@report_call` and `JET.@report_opt`. See the [guide](guide.md#JET).

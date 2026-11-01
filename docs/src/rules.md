# Rules

A rule name is the label you pass to [`ratchet!`](@ref) and write in opt-out comments. The names
below are conventions; any lowercase words joined by `-` work.

Rules that need the compiler's answer read a loaded module. Rules about how code is written read
source files.

## Rules on a loaded module

These see inferred types, bindings and closures. They need `using MyPackage`. The rules that read
inferred types take their signatures from the caller: `inferred_methods(MyPackage, signatures)` infers the
methods those signatures reach, so the result is the same on every run. `inferred_methods(MyPackage,
entry_frames(seeds, MyPackage))` reads the frames an entry-point walk already inferred. The `corset`
command line has no signatures, so it skips these rules. An opt-out on a method's first line covers
every site these rules find in that method.

### `hidden-input`: `hidden_inputs(mod)`

Reads of a non-constant or mutable global, or of a `ScopedValue`. The result of such a function
depends on state its signature does not show.

Repair: pass the value as an argument, or return it from the function that computes it.

### `non-public-access`: `non_public_accesses(mod)`

Pedantic. Qualified accesses (`Base.JuliaSyntax`) and explicit imports (`using Base: uniontypes`)
of a name its module neither exports nor declares `public`. Such a name can change in any release.
ExplicitImports.jl finds them. A qualified access has a site per use, so an opt-out covers only its line.

Repair: use a public name, or opt the line out with the reason the internal is needed.

### `abstract-local`: `abstract_locals(repo, inferred_methods(mod, signatures))`

Local variables whose inferred type is abstract or a union, one site per variable however many
specializations ran. The usual causes are an accumulator that starts as `0` and receives floats, and
a variable assigned from a container of abstract type.

Repair: initialize with the right type (`zero(eltype(xs))`) or annotate the local.

### `bang`: `unmarked_effects(repo, inferred_methods(mod, signatures))`

Functions that always return `nothing` and have no `!` in the name. A function with a `nothing`
method beside methods that return values (a dispatch on "off") is not reported.

Repair: add the `!`.

### `unmarked-mutation`: `unmarked_mutations(repo, inferred_methods(mod, signatures))`

Functions without `!` in the name that write through an argument: `v[1] = 0`, `x.field = 1`,
`push!(x.items, 1)`, or a write through an alias, a field or an element of the argument. The rule reads each
frame's optimized IR and asks the compiler's escape analysis which arguments the written object
aliases. A callee that is not inlined writes its first argument when its name ends in `!`, and what its own frame writes otherwise.
At a runtime dispatch the rule lists the candidate methods (`candidate_limit`, default 4, in the
`[preferences.Corset]` table, `--candidate-limit` on the command line, or
`unmarked_mutations(repo, inferred; search = CandidateSearch(inferred; candidate_limit))`). When every
candidate is listed and none writes the argument, the dispatch writes nothing. A candidate that writes it
makes the write definite, and the detail names the candidate. An argument passed to a `ccall`, or to a
dispatch with more candidates than the budget, a candidate inference cannot type, or a candidate that
itself dispatches on the argument, is reported as one that may be written. `runtime-dispatch` reports the same dispatch.
A method the package adds to another module's non-`!` function (`Base.length`, `Base.iterate` on a stateful iterator) is checked too: "adds a writing method to `Base.length`, which callers expect not to write". A write to any Julia object counts, an `IOBuffer`, a lock or a `Channel` included. Arguments that cannot
be written in Julia are never reported: plain immutable data (bits values, `String`s, `Symbol`s), types,
modules, and OS-backed handles (`IOStream`, files, pipes, sockets, terminals, processes), whose writes
leave Julia. So is an `IOContext` around one. A method declaring an abstract `IO` argument (`io::IO`) writes whatever stream its caller passes, so it is not reported even when compiled for an `IOBuffer`; a concrete in-memory declaration (`io::IOBuffer`, `io::IOContext{IOBuffer}`) is.
Escape analysis merges the alias sets of a value and the object it is stored in, so `deepcopy_internal(x, stackdict)`,
which stores `x` in `stackdict`, reports both.

Repair: add the `!`, or copy the argument before writing to the copy.

### `runtime-dispatch`: `runtime_dispatches(repo, inferred_methods(mod, entry_frames(seeds, mod)))`

Pedantic. Calls the optimizer leaves to run-time dispatch in each frame: a `:call` of a generic
function, or of `Core._apply_iterate` or `Core.invoke`. A logging macro's hand-off to the current
logger is not reported. Pass the frames of `entry_frames`, so a `@noinline` callee reached only through
an `:invoke` edge is read too. One site per method and source line.

Repair: make the callee's argument types inferable, or put a function barrier around the untyped part.
Opt out a deliberate barrier on the method's first line.

### `widened-return`: `widened_returns(repo, inferred_methods(mod, entry_frames(seeds, mod)))`

Pedantic. Methods whose inferred result a caller cannot compile against: anything but a concrete
type, `Union{}`, a `Type{X}` constant, a union of at most four concrete types, or a fixed-length tuple
of such members.

Repair: make the result type depend only on the argument types.

### `float-widening`: `float_widenings(repo, inferred_methods(mod, entry_frames(seeds, mod)))`

Pedantic. Statements whose float result is wider than every float the method receives in its
arguments: `x::Float32 * 2.0`, `n / m` on `Int`s in a `Float32` method, `float(n)`, a `Float64`
global, or a returned `0.0`. The detail names the operand that brings the wide float in (`Base.Float64`
for a conversion, `0.0`, the global), or the callee. A value computed from an already widened one is
not reported again. Methods with no float argument, or one already as wide as `Float64`, are skipped.
Arguments count the floats they hold anywhere in their type (`Vector{Float32}`, `Complex{Float16}`).

At a runtime dispatch the rule lists the candidate methods (`candidate_limit`, as in
`unmarked-mutation`). A candidate that returns a wider float makes the site definite. A dispatch with
more candidates than the budget, or one inference cannot type, may widen: "may widen
(`runtime-dispatch`)". A dispatch whose argument types cannot hold the method's floats is skipped.

`float64` finds the same literals and tokens in the source text of every method; this rule reads what
the compiler made of them, for the argument types given. [`float64_ops`](@ref) counts the Float64
operations of one call.

Repair: `oftype(x, 2.0)`, `T(0.5)` or `float(T)(n)`, with `T` the argument's float type.

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
| `float64` | `float64_sites(file)` | `Float64` tokens and untyped float literals; `float-widening` reads where they widen a narrower argument | `zero(T)`, `T(0.5)` or `oftype(x, 0.5)` |
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

### `jscpd`: `jscpd_sites(repo, directories)`

One site per duplicate code block found by [jscpd](https://github.com/kucherenko/jscpd), keyed by
the duplicate file and the duplicated file, placed at the duplicate block's lines. `jscpd` must be
on `PATH`; the rule errors if it is not.

### `jet`: [`@call_sites`](@ref), [`@opt_sites`](@ref)

Reports of `JET.@report_call` and `JET.@report_opt`. See the [guide](guide.md#JET).

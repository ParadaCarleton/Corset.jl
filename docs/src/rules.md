# Rules

A rule name is the label you pass to [`offenders!`](@ref) and write in opt-out comments. The names
below are conventions; any lowercase words joined by `-` work.

Rules that need the compiler's answer read a loaded module. Rules about how code is written read
source files.

## Groups

The `corset` command runs the `default` group at `warn` level. `--pedantic`, or `pedantic = true` in
the configuration, adds the `pedantic` group. Julia permits what Rust's compiler rejects; a `default`
rule finds a pattern Rust rejects or requires an explicit marker for (`dyn`, `mut`, `unsafe`, typed
signatures, privacy), a likely bug, or a performance trap. A `# lint:` opt-out is the explicit marker.
A `pedantic` rule enforces house style that Rust allows, or is a noisy heuristic.

| Group | Rules |
| --- | --- |
| `default` | `abstract-field`, `abstract-local`, `annotation`, `bang`, `broad-catch`, `concrete-arg`, `derived-constant`, `fatou`, `float-widening`, `forbidden-pattern`, `hidden-input`, `impure-anonymous-function`, `jet`, `misplaced-import`, `mutable-struct`, `non-atomic-write`, `non-public-access`, `overspecialized-anonymous-function`, `quadratic-vcat`, `recursion-limit`, `repeated-statement`, `return-type`, `runtime-dispatch`, `unmarked-mutation`, `unstable-anonymous-function`, `where-return`, `widened-return` |
| `pedantic` | `c-type`, `concrete-return`, `constant-array`, `file-length`, `float64`, `jscpd`, `nan-initializer`, `nothing-return`, `one-letter`, `quadratic-scan`, `range-guard`, `ref`, `repeated-prefix`, `similar-array`, `struct-constant`, `wide-struct` |

`corset rules` prints each rule's group and level. `[preferences.Corset.levels]` and the `--allow`,
`--warn` and `--deny` flags set the level of one rule.

## Rules on a loaded module

These see inferred types, bindings and closures. They need `using MyPackage`. The rules that read
inferred types take their signatures from the caller: `entry_frames(signatures, MyPackage)` infers the
package's methods those signatures reach, so the result is the same on every run. Submodules and
loaded extensions count as the package. The `corset` command line seeds that walk from
`Corset.Entries` (see `--entries` in the CLI page). An opt-out on a method's first line covers
every site these rules find in that method.

### `hidden-input`: `hidden_inputs(repository, mod)`

Reads of a non-constant or mutable global, or of a `ScopedValue`. The result of such a function
depends on state its signature does not show.

Repair: pass the value as an argument, or return it from the function that computes it.

### `non-public-access`: `non_public_accesses(mod)`

Qualified accesses (`Base.JuliaSyntax`) and explicit imports (`using Base: uniontypes`)
of a name its module neither exports nor declares `public`. Such a name can change in any release.
ExplicitImports.jl finds them. A qualified access has a site per use, so an opt-out covers only its line.

Repair: use a public name, or opt the line out with the reason the internal is needed.

### `abstract-local`: `abstract_locals(repo, entry_frames(signatures, mod))`

Local variables whose inferred type is abstract or a union, one site per variable however many
specializations ran. The usual causes are an accumulator that starts as `0` and receives floats, and
a variable assigned from a container of abstract type.

Repair: initialize with the right type (`zero(eltype(xs))`) or annotate the local.

### `bang`: `unmarked_effects(repo, entry_frames(signatures, mod))`

Functions that always return `nothing` and have no `!` in the name. A function with a `nothing`
method beside methods that return values (a dispatch on "off") is not reported.

Repair: add the `!`.

### `unmarked-mutation`: `unmarked_mutations(repo, entry_frames(signatures, mod))`

Functions without `!` in the name that write through an argument: `v[1] = 0`, `x.field = 1`,
`push!(x.items, 1)`, or a write through an alias, a field or an element of the argument. The rule reads each
frame's optimized IR and asks the compiler's escape analysis which arguments the written object
aliases. A callee that is not inlined writes its first argument when its name ends in `!`, and what its own frame writes otherwise.
At a runtime dispatch the rule lists the candidate methods (`candidate_limit`, default 4, in the
`[preferences.Corset]` table, `--candidate-limit` on the command line, or
`unmarked_mutations(repo, inferred; search = CandidateSearch(inferred; candidate_limit))`). When every
candidate is listed and none writes the argument, the dispatch writes nothing. A candidate that writes it
makes the write definite, and the detail names the candidate. A `ccall` of a C function whose writes are
known (`jl_genericmemory_copyto`, which `copyto!` and `vcat` of boxed elements call, and `memmove`, `memcpy`,
`memset`, `strlen`, `memcmp`, `memchr`, `strcmp`, `strncmp`) reads its sources; only its destination may be written.
A `Ptr` operand counts as the argument it points into (`pointer(x)`, the conversion `ccall` applies to `x`),
and `unsafe_store!` through such a pointer writes the argument. A `Cstring` operand is read.
An argument passed to any other `ccall`, or to a
dispatch with more candidates than the budget, a candidate inference cannot type, or a candidate that
itself dispatches on the argument, is reported as one that may be written. `runtime-dispatch` reports the same dispatch.
A method the package adds to another module's non-`!` function (`Base.length`, `Base.iterate` on a stateful iterator) is checked too: "adds a writing method to `Base.length`, which callers expect not to write". A write to any Julia object counts, an `IOBuffer`, a lock or a `Channel` included. Arguments that cannot
be written in Julia are never reported: plain immutable data (bits values, `String`s, `Symbol`s), types,
modules, and OS-backed handles (`IOStream`, files, pipes, sockets, terminals, processes), whose writes
leave Julia. So is an `IOContext` around one. A method declaring an abstract `IO` argument (`io::IO`) writes whatever stream its caller passes, so it is not reported even when compiled for an `IOBuffer`; a concrete in-memory declaration (`io::IOBuffer`, `io::IOContext{IOBuffer}`) is.
Escape analysis merges the alias sets of a value and the object it is stored in, so `deepcopy_internal(x, stackdict)`,
which stores `x` in `stackdict`, reports both.

Repair: add the `!`, or copy the argument before writing to the copy.

### `runtime-dispatch`: `runtime_dispatches(repo, entry_frames(seeds, mod))`

Calls the optimizer leaves to run-time dispatch in each frame: a `:call` of a generic
function, or of `Core._apply_iterate` or `Core.invoke`. A logging macro's hand-off to the current
logger is not reported. Pass the frames of `entry_frames`, so a `@noinline` callee reached only through
an `:invoke` edge is read too. One site per method and source line.

Repair: make the callee's argument types inferable, or put a function barrier around the untyped part.
Opt out a deliberate barrier on the method's first line.

### `recursion-limit`: `recursion_limits(repo, entry_frames(seeds, mod), mod)`

Calls to a method of the package that inference cut off at its recursion limit, because the
argument types nest deeper with every call:

```julia
grow(x, n::Int) = n == 0 ? x : grow((x,), n - 1)   # Int, Tuple{Int}, Tuple{Tuple{Int}}, …
```

The cut-off callee keeps no inferred code, so it is never optimized together with its caller, and
each depth infers and compiles a new specialization. The site is the call, in the frame where
inference stopped. JET's optimization analysis reports the frames past it as
`OptimizationFailureReport`. `entry_frames` follows no instance of a cut-off method, so its walk
ends on such code. A cut-off call to another module's method (Base's `Dict` built from a
generator over untyped data, say) is not reported.

Repair: keep the argument types fixed across the recursion (a loop, or an accumulator of one type),
or put a function barrier where the type is allowed to change.

### `widened-return`: `widened_returns(repo, entry_frames(seeds, mod))`

Methods whose inferred result a caller cannot compile against: anything but a concrete
type, `Union{}`, a `Type{X}` constant, a union of at most four concrete types, or a fixed-length tuple
of such members.

Repair: make the result type depend only on the argument types.

### `float-widening`: `float_widenings(repo, entry_frames(seeds, mod))`

Statements whose float result is wider than every float the method receives in its
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
| `impure-anonymous-function` | `impure_anonymous_functions(repo, mod)` | a mutable capture (an array, `Dict`, `Ref`, a module); a `Core.Box`, a captured variable rebound; no compiled instance, so the captures are unverified | pass the data as an argument, or use `Base.Fix1`/`Base.Fix2` (`filter(in(allowed), items)`); cover an unverified function in the precompile workload |
| | | with `Repository.strict_captures`: any capture, plain immutable data included | pass it as an argument |
| `unstable-anonymous-function` | `unstable_anonymous_functions(repo, mod)` | a capture whose type inference left abstract, or an instance built where the capture types are unknown | make the captured variable's type concrete, or pass it as an argument |
| `overspecialized-anonymous-function` | `overspecialized_anonymous_functions(repo, mod)` | a captured type or function: the anonymous function compiles anew for every value | pass it as an argument, or define a callable struct whose field is a `DataType` or `Function` |

### `abstract-field`: `abstract_fields(type)`, `repeated-prefix`: `repeated_prefix(type)`

Both take a struct type. Apply them to every struct a module defines with `module_structs(mod)` and
place each site with `struct_site(T, struct_locations(Corset.Source.(files)))`.

- `abstract_fields` finds fields declared with an abstract type, or with a concrete container of one:
  `Vector{Any}`, `Base.RefValue{Any}` and `Dict{Tuple, Any}` are concrete, but every read from them is
  dynamically dispatched. Repair: make the field type a type parameter of the struct.
- `repeated_prefix` finds field names that repeat a word the type should say once. Fields
  `continuation_step` and `continuation_theta` belong in a `ContinuationControls`.

`mutable-struct` reports every struct of `mutable_structs(mod)`. Repair: return the changed data from
the function that computes it and keep the struct immutable. A struct that needs a finalizer, a
cyclic reference or a lock's identity opts out with `# lint: mutable-struct` and a reason.
`wide-struct` reports structs with more than `Repository.struct_field_limit` fields (default 12).
Repair: group related fields into a struct of their own.

`struct-constant` reports constants of the package that hold a struct it defines, or alias a type naming
one (`const Alias = Union{Nothing, Setting}`): Revise rebuilds a revised struct but not an unchanged
constant built from it. `derived-constant` reports a constant whose value calls a function the package
defines, which Revise does not re-evaluate until the constant's own text changes. Repair: build the value
in a function, and spell an alias at its use sites.

```julia
files = repository_sources(REPO, ("src",))
locations = struct_locations(Corset.Source.(files))
sites = [struct_site(T, locations) for T in module_structs(MyPackage) if !isempty(abstract_fields(T))]
offenders!(REPO, "abstract-field", sites)
```

## Rules on source files

Each takes `Corset.Source(repo, file)`, the file read and parsed once.

| Rule | Function | Finds | Repair |
| --- | --- | --- | --- |
| `nothing-return` | `nothing_returns` | declared `Union{Nothing, …}` results | return a value that always means something, or throw |
| `range-guard` | `range_guards` | `floatmin`/`floatmax`, `exp`'s range edges (88, 709), `isfinite(exp(…))` | compute in log space or clamp at the source |
| `repeated-statement` | `repeated_statements` | a statement repeated in one block; the same line in two branches passes | delete the copy |
| `return-type` | `return_type_calls` | calls of `Core.Compiler.return_type`, a guess at a result type | restructure so the type is known |
| `concrete-arg` | `concrete_arguments` | arguments annotated `Vector`, `Matrix`, `Array` or `Dict` that the method never resizes | `AbstractVector{T}` and the like; they accept views, `OffsetArray` and GPU arrays |
| `concrete-return` | `concrete_returns(source, mod)` | result types that name a concrete type, `Vector{E}` included; `AbstractMatrix{T}` passes; a constructor returning its own type is exempt | annotate by what the arguments bind; `Corset.CONCRETE_RETURN_FIX` is the log text |
| `annotation` | `missing_annotations` | methods with an unannotated argument or result | annotate |
| `float64` | `float64_sites(source)` | `Float64` tokens and untyped float literals; `float-widening` reads where they widen a narrower argument | `zero(T)`, `T(0.5)` or `oftype(x, 0.5)` |
| `ref` | `ref_sites(source)` | `Ref` and `RefValue` outside `ccall`, `@ccall`, `cfunction`, `@cfunction` and `@ccallable` | Return the changed data from the function that computes it. A broadcast shield (`f.(Ref(x), xs)`) opts out with `# lint: ref` |
| `c-type` | `c_type_sites(source)` | `Cint`, `Cdouble` and the other C-interop types outside `ccall`, `@ccall`, `cfunction`, `@cfunction` and `@ccallable` | `Int`, `Float64` or `String`; convert at the `ccall` |
| `one-letter` | `one_letter_sites(repo, source)` | one-letter variable names (exempt: `_` and `Repository.one_letter_exempt`) | name the variable |
| `file-length` | `long_file_sites(repo, source)` | source files longer than `Repository.file_line_limit` lines (default 1500) | split the file by topic |
| `broad-catch` | `broad_catches(source)` | `catch` blocks that neither call `rethrow()` nor `throw` what they caught, so a missing file and an internal `error()` end alike; placed from the `try` line to the block's first line | test the exception with `isa`, handle the expected types and `rethrow()` the rest |
| `quadratic-scan` | `quadratic_scans(source)` | a `for` loop, comprehension, generator, anonymous function passed to `map`, `count` and the like, or broadcast over a collection `xs` (a variable or field, also through `enumerate`, `zip` and `eachindex`) that calls `filter`, `findall`, `findfirst`, `findlast`, `count`, `any`, `all` or `in` on the same `xs` per element; `in.(xs, (xs,))` too | group `xs` once: a `Dict` from key to entries, or `sort` and `searchsorted` |
| `constant-array` | `constant_array_sites(sources)` | `zeros`, `ones`, `fill`, `trues` and `falses` of an array no code writes (a written buffer, a StaticArrays type and a `fill` of a mutable value are exempt) | `Zeros`, `Ones`, `Fill`, `Trues`, `Falses` from FillArrays.jl; `--unsafe-fixes` also rewrites arrays that leave their function |
| `nan-initializer` | `nan_initializer_sites(sources)` | `zeros`, `ones` and `fill` of an array that is then written (an array only accumulated into, `x[i] += …`, is exempt) | `fill(T(NaN), dims…)` when every element is provably written before any read; other written arrays are reported only; with a `length(x)` or `size(x)` dimension of a parameter annotated as an array, `fill!(similar(x, T, dims), NaN)` |
| `similar-array` | `similar_array_sites(sources)` | `Vector{T}(undef, …)`, `Matrix{T}(undef, …)`, `Array{T}(undef, …)`, `Vector{T}(x)`, which name a concrete container (an empty `T[]` or `Vector{T}()` has no template and is exempt) | none under `--fix` (a sparse or device template changes the result type); `similar_array_plan` rewrites `C{T}(undef, length(x))` and `C{T}(undef, size(x))` to `similar(x, T, dims)` for a reviewed diff, where `x` is a parameter annotated as an array that the body never rebinds and the buffer is no `copyto!`/`copy!` destination. A conversion names `collect(x)` or `collect(T, x)`; `Matrix{T}(I, n, n)`, filled forms and untyped `Array(x)` (host transfer) are exempt |
| `quadratic-vcat` | `quadratic_concatenations(source)` | a fold whose operator is `vcat`, `hcat`, `cat` or `hvcat` that runs one piece at a time: `reduce` with `init` (Base's one-allocation `reduce(vcat, ::AbstractVector{<:AbstractVector})` then does not apply) or over a generator, and every `foldl`, `foldr`, `mapreduce`, `mapfoldl` and `mapfoldr`, `do` form included. Each step copies the accumulator, so the fold is quadratic in the total length | `collect(T, Iterators.flatten(pieces))`, a flattening comprehension `T[x for piece in pieces for x in piece]`, or `reduce(vcat, pieces)` on a nonempty vector |
| `non-atomic-write` | `non_atomic_writes(source)` | `write.(paths, texts)`, `foreach(write, paths, texts)`, and loops, comprehensions and mapped anonymous functions whose body calls `write(path, …)` or `open(path, "w")` (also `"a"`, `"w+"`, `"a+"`, `"r+"`, `write = true`, `append = true`, `truncate = true`) on a path built from the iteration variable; a crash halfway leaves some files rewritten. A function that calls `mv` or `rename` stages its writes and passes | compute every text, write each to a temporary file beside its target, then rename them all (`Corset.write_all!`) |
| `forbidden-pattern` | `forbidden_pattern_sites(repo, source)` | lines that match a `Repository.forbidden_patterns` entry (`name`, `pattern`, `message`, optional `unless`, `skip_files`) | what the entry's `message` says |

## Rules with fixers

Three rules come with a fixer. `Corset.fix!(rule, repo, directories)` applies one: the rule's
`fix_plan` proposes one repair per site, and `fix!` drops every repair a `# lint:` comment opts out
(line, block and file forms) before it writes. It computes every file before it writes any, and
returns the sites it repaired.

### `misplaced-import`: `misplaced_imports(repo, directories)`

Imports that their file does not use, or that only other files of the module use. An import item
belongs in the files that use its name. Its fixer deletes the unused ones and moves the rest.
A name counts as used only in the innermost `module` block that uses it, since a module sees only its
own imports; so no import moves into a file that holds only `module` blocks. A file included inside a
`module` block belongs to that block's module: it takes only the block's imports. A name that a relative import
(`using ..Parent: f`, `import .Sub.g`) takes from another module of the package keeps its imports.

### `constant-array`: `constant_array_sites(sources)`

Calls of `zeros`, `ones`, `fill`, `trues` and `falses` (also `Base.zeros` and the like) that build an
array no code writes. [FillArrays.jl](https://github.com/JuliaArrays/FillArrays.jl) stores such an array as
one value: `Zeros`, `Ones`, `Fill`, `Trues` and `Falses`.

A FillArrays array is immutable, so a written buffer has no such form and the rule stays silent on it.
An array counts as written when its variable is assigned through (`x[i] = …`, `x .= …`, `@. x = …`), passed
to a function whose name ends in `!`, or declared with a type (`x::Vector{Float32} = zeros(…)`). `fill` of
an array, dictionary or comprehension aliases it, so the rule leaves that alone too.

An array that leaves its function (returned, stored in a struct, bound at the top level, passed to a
function without `!`, viewed or sliced) may be written elsewhere. The rule reports it, and only
`--unsafe-fixes` rewrites it. An array stored under a name some file writes through (`set_sizes` in
`(; set_sizes = zeros(n))` when any code runs `set_sizes[i] = …` or `a.set_sizes[i] = …`) counts as written.
The fixer rewrites the rest, adds `using FillArrays: Zeros, …` after the last import of each module (or at
the top of its body), and lists `FillArrays` in the `[deps]` of the nearest Project.toml.

An index counts as a scalar only when it is an integer literal, `end` or a sum of them: `x[i]` may be a
vector slice, which is a `Fill` that a later write cannot change. `first(x, n)`, `last(x, n)` and any
reader called with a keyword (`sum(x; dims = 1)`) return arrays, and `zero(x)` of an array is an array.

### `nan-initializer`: `nan_initializer_sites(sources)`

A `zeros`, `ones` or `fill` array that is then written holds a made-up start value, so an element no write
reached passes for data. NaN shows it. The fixer rewrites `zeros(T, dims…)` and `ones(T, dims…)` as
`fill(T(NaN), dims…)` (`fill(NaN, dims…)` for the default Float64) and `fill(v, dims…)` with a literal or
`zero(T)`/`one(T)` value likewise, but only when it proves that every element is written before any read: the
first statement after the binding that mentions the array is either `x .= rhs`, or a `for` loop over every
index (`eachindex(x)`, or `axes(x, d)` per dimension) whose first statement mentioning `x` is
`x[i, …] = rhs`, with `rhs` free of `x` and no `break`, `continue` or `return` in the loop.

The rule reports without fixing a written array it cannot prove such an initializer, since an unwritten element may be
read as its start value, and every integer or Bool array, which has no NaN (pick a sentinel by hand).
An array accumulated into (`x[i] += …`, `x .+= …`) reads its start value and is silent, as is an array no code writes
(`constant-array` covers that).

### `where-return`: `where_return_sites(file)`

Short-form definitions whose `where` binds the return annotation:

```julia
f(x::T)::T where {T} = x      # parses as f(x::T)::(T where {T}); T is not the method's T
(f(x::T)::T) where {T} = x    # what was meant
```

Its fixer parenthesizes those whose `where` binds a variable of the arguments.

### `quadratic-vcat`: `quadratic_concatenations(file)`

Its fixer rewrites `reduce(vcat, pieces; init = T[])` as `collect(T, Iterators.flatten(pieces))`, and
the folds inside `pieces` with it. It leaves `init = Any[]` and every other fold alone: `vcat` appends a
piece that is not a vector whole, where `flatten` iterates it, and only a `T` other than `Any` turns that
difference into a conversion error instead of a different result.

## Rules that call other tools

### `fatou`: `fatou_sites(repo, directories)`

One site per finding of [Fatou](https://github.com/jolars/fatou)'s `fatou lint`, keyed by file and
Fatou rule. `fatou` must be on `PATH`; the rule errors if it is not.

### `jscpd`: `jscpd_sites(repo, directories)`

One site per duplicate code block found by [jscpd](https://github.com/kucherenko/jscpd), keyed by
the duplicate file and the duplicated file, placed at the duplicate block's lines. `jscpd` must be
on `PATH`; the rule errors if it is not.

### `jet`: `call_report_sites(repo, entry_frames(seeds, mod), mod)`, [`@call_sites`](@ref), [`@opt_sites`](@ref)

Reports of JET's error analysis, `JET.report_call`: a call no method matches, an undefined global or
field, a call that always throws. The `corset` command runs it on every frame `entry_frames` keeps,
when the load path finds JET: the project's environment, Corset's, or the default environment
(`@v#.#`). Corset does not depend on JET; without it the rule is listed as skipped. A report counts
when its innermost frame is a method of the package (JET's `target_modules`), and is keyed by that
method and the report's kind and placed at its line, so an opt-out goes on the reported line. The
same report reached from several frames is one site.

The rule leaves out `JET.report_opt`: `runtime-dispatch` reports its runtime dispatches,
`impure-anonymous-function` its captured `Core.Box`es, and `recursion-limit` the calls where its
optimization failures start. In tests, [`@call_sites`](@ref) and
[`@opt_sites`](@ref) run either analysis on one call. See the [guide](guide.md#JET).

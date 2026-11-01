# Corset

[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://paradacarleton.github.io/Corset.jl/dev/)

Code-quality rules for Julia packages, run as tests. A rule reads a loaded module (its lowered and
inferred code, bindings and types) or a source file, and returns the places where the code breaks it.
`ratchet!` turns those places into one `@test`.

Corset checks what a linter cannot see because it needs the compiler's answer: a local that infers as
a union, a closure that boxes a captured variable, a function that reads a mutable global, a Float32
kernel that computes in Float64.

```julia
pkg> add Corset
```

```julia
using Test
using Corset: Repository, ratchet!, hidden_inputs, abstract_locals, inferred_methods
using MyPackage

const REPO = Repository(pkgdir(MyPackage); baseline = joinpath(@__DIR__, "code_baseline.toml"))

@testset "code rules" begin
    ratchet!(REPO, "hidden-input", hidden_inputs(MyPackage))
    ratchet!(REPO, "abstract-local", abstract_locals(REPO, inferred_methods(MyPackage, SIGNATURES)))
end
```

`SIGNATURES` is the fixed list of method signatures the rules type the package over (for example
`Tuple{typeof(solve), Float32}`), so the result does not change with test order.
`entry_frames(seeds, MyPackage)` builds the workload from entry-point call signatures: it walks their
optimized IR along `:invoke` edges and returns every frame they compile, inferred once.
`inferred_methods(MyPackage, entry_frames(seeds, MyPackage))` reads those frames without inferring again.

The baseline file allows today's offenders, fails on new ones and lowers itself as old ones are fixed.
The [documentation](https://paradacarleton.github.io/Corset.jl/dev/) has the guide (baselines,
exemptions, opt-out comments) and the reference for every rule.

# Corset

[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://paradacarleton.github.io/Corset.jl/dev/)

Code-quality rules for Julia packages, checked in CI by `corset check`. A rule reads a loaded module
(its lowered and inferred code, bindings and types) or a source file, and returns the places where the
code breaks it.

Corset checks what a linter cannot see because it needs the compiler's answer: a local that infers as
a union, a closure that boxes a captured variable, a function that reads a mutable global, a Float32
kernel that computes in Float64.

```julia
pkg> add Corset
```

Run it in a CI job of its own. With Corset in the package's test dependencies:

```bash
julia -e 'using Pkg; Pkg.add("TestEnv")'
julia --project=. -e 'using TestEnv; TestEnv.activate(); using Corset; exit(Corset.main(ARGS))' -- check .
```

`corset check` loads the package in a fresh process, without `--code-coverage`, so the typed rules
read the code users run. They type the package over its entry-point signatures: the specializations
its precompile workload compiles and the methods whose declared signature is already concrete.
`entry_frames` walks their optimized IR along `:invoke` edges and inlined callees, and returns the
frame of every method instance of the package they reach, inferred once.

A baseline file allows today's offenders and fails on new ones; `corset baseline`
seeds it and lowers it as old ones are fixed. The
[documentation](https://paradacarleton.github.io/Corset.jl/dev/) has the guide (baselines,
exemptions, opt-out comments) and the reference for every rule.

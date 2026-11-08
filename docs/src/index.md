# Corset.jl

Corset checks a package against code-quality rules. A rule is a function that reads a loaded module
(its lowered and inferred code, bindings and types) or a source file, and returns the places where
the code breaks it. [`corset check`](cli.md) runs the rules in CI.

Corset checks things a linter cannot see because they need the compiler's answer: a local variable
that infers as `Any`, a closure that boxes a captured variable, a function that reads a mutable
global, a Float32 kernel that computes in Float64.

## Install

```julia
pkg> add Corset
```

## A first check

Write a module with two problems.

```@setup first
using Corset: Repository, offenders!, hidden_inputs, unstable_variables, entry_frames
root = mktempdir()
mkpath(joinpath(root, "src"))
write(joinpath(root, "src", "Demo.jl"), """
module Demo
const COUNTER = Ref(0)
bump(x) = x + COUNTER[]
function total(xs)
    acc = 0
    for x in xs
        acc += x / 2
    end
    acc
end
end
""")
include(joinpath(root, "src", "Demo.jl"))
```

```julia
module Demo
const COUNTER = Ref(0)
bump(x) = x + COUNTER[]

function total(xs)
    acc = 0
    for x in xs
        acc += x / 2
    end
    acc
end
end
```

`bump` reads a mutable global, so its result depends on state its signature does not show. In
`total`, `acc` starts as an `Int` and becomes a `Float64`, so the compiler infers a union for it.
Ask Corset for the offenders of the two rules that notice this:

```@example first
repo = Repository(root)
offenders!(repo, "hidden-input", hidden_inputs(repo, Demo))
```

```@example first
offenders!(repo, "unstable-variable", unstable_variables(repo, entry_frames([Tuple{typeof(Demo.total), Vector{Int}}], Demo)))
```

Each returned string is a key: the name of one offender. [`offenders!`](@ref) returns the keys
and logs them.

## In CI

[`corset check`](cli.md) runs every rule over a package and exits nonzero on a finding. Give it a CI
job of its own; with Corset in the package's test dependencies:

```bash
julia -e 'using Pkg; Pkg.add("TestEnv")'
julia --project=. -e 'using TestEnv; TestEnv.activate(); using Corset; exit(Corset.main(ARGS))' -- check .
```

With no further setup every offender fails. A package with existing offenders adopts Corset one
rule at a time through a [baseline](guide.md#Adopting-Corset-on-an-existing-package). The
[Guide](guide.md#Where-to-run-the-rules) says why the rules run outside `Pkg.test`.

## Where to go next

- [Guide](guide.md): where to run the rules, baselines, exemptions and opt-out comments.
- [Rules](rules.md): every rule, what it finds and how to repair an offender.
- [API](api.md): the exported names. The internals pages hold every other docstring.

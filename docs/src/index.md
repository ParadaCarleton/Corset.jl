# Corset.jl

Corset turns code-quality rules into tests. A rule is a function that reads a loaded module (its
lowered and inferred code, bindings and types) or a source file, and returns the places where the
code breaks it. [`ratchet!`](@ref) turns those places into one `@test`.

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
using Corset: Repository, offenders!, hidden_inputs, abstract_locals, inferred_methods
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
offenders!(repo, "abstract-local", abstract_locals(repo, inferred_methods(Demo, [Tuple{typeof(Demo.total), Vector{Int}}])))
```

Each returned string is a key: the name of one offender. [`offenders!`](@ref) returns the keys
and logs them; [`ratchet!`](@ref) does the same and fails a test if there are any.

## In a test suite

```julia
using Test
using Corset: Repository, ratchet!, hidden_inputs, abstract_locals, inferred_methods
using MyPackage

const REPO = Repository(pkgdir(MyPackage))

@testset "code rules" begin
    ratchet!(REPO, "hidden-input", hidden_inputs(REPO, MyPackage))
    ratchet!(REPO, "abstract-local", abstract_locals(REPO, inferred_methods(MyPackage, SIGNATURES)))
end
```

With no further setup every offender fails. A package with existing offenders adopts Corset one
rule at a time through a [baseline](guide.md#Adopting-Corset-on-an-existing-package).

## Where to go next

- [Guide](guide.md): wiring rules into `runtests.jl`, baselines, exemptions and opt-out comments.
- [Rules](rules.md): every rule, what it finds and how to repair an offender.
- [API](api.md): the exported names. The internals pages hold every other docstring.

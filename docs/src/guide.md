# Guide

## The pieces

A **rule** is a function from code to a vector of [`Site`](@ref)s. A site has a `key` (the name of
the offender, such as `"Demo.jl total"`), a file, a line and a `detail` (what the offender is, such as
``local `x`::Any``; `""` when the key says it all). The log of a failing rule prints each key's details.

A **[`Repository`](@ref)** is the tree the rules read, plus the settings that relax them.

[`ratchet!`](@ref)`(repo, "rule-name", sites)` holds the sites to the repository's allowances and
runs one `@test`. The rule name is a label you choose. It names the rule's table in the baseline file
and the rule in opt-out comments. [`offenders!`](@ref) does the same without the `@test`.

There are two kinds of rules.

- **Module rules** read a loaded module: `hidden_inputs(repository, MyPackage)`, `impure_anonymous_functions(MyPackage)`,
  `abstract_locals(repo, inferred_methods(MyPackage, SIGNATURES))`.
- **Source rules** read a file's syntax. Parse each file once with `located_source`, then hand it to
  each rule: `nothing_returns(file, located_source(file))`. `repository_sources(repo, ("src",))`
  lists a repository's files.

```julia
@testset "code rules" begin
    files = repository_sources(REPO, ("src",))
    ratchet!(REPO, "nothing-return",
        [site for file in files for site in nothing_returns(file, located_source(file))])
end
```

## Adopting Corset on an existing package

Turning on a rule in a mature package usually reports hundreds of offenders. A **baseline** makes
that adoptable. It allows today's offenders, fails on new ones, and lowers itself as old ones are
fixed.

```julia
const REPO = Repository(pkgdir(MyPackage); baseline = joinpath(@__DIR__, "code_baseline.toml"))
```

Create an empty `code_baseline.toml` and run the tests. A rule without a table is seeded with its
current offenders and passes:

```toml
[hidden-input]
"COUNTER" = 1

[abstract-local]
"Demo.jl total" = 1
```

Each entry is a key and an allowance. An integer allows that many sites under the key. A string,
such as `"kept: hot loop"`, is a note that allows any number.

After that:

- A **new** offender fails the test, because its key has no entry or the entry's count is exceeded.
- A **fixed** offender lowers the file. When a run finds fewer sites than an entry allows, the entry
  falls to the new count, or is deleted at zero, and the file is rewritten. Commit the change. The
  allowance can only shrink.

A testset that measures only part of a rule's keys passes the key prefixes it covers as `scopes`, so
entries outside them never fall.

```julia
ratchet!(REPO, "abstract-local", sites; scopes = ("Parser.jl",))
```

## Telling the reader how to repair an offender

`fix` adds a line to the failure log:

```julia
ratchet!(REPO, "concrete-return", sites; fix = Corset.CONCRETE_RETURN_FIX)
```

## Exemptions

Two settings on the [`Repository`](@ref) relax rules for a whole project:

```julia
Repository(root; one_letter_exempt = (:p,), skipped_directories = ("vendor",))
```

`one_letter_exempt` lists variable names the one-letter rule allows besides `_`. A project's own
convention, such as an argument everywhere named `p`, goes here. `skipped_directories` lists
directory names that `repository_sources` leaves out wherever they sit. Hidden directories are
always left out.

## Opting out one site

A comment opts a site out of a rule by the rule's name:

```julia
const CACHE = Ref(0)   # lint: hidden-input  memoized across calls on purpose
```

| Comment | Opts out |
| --- | --- |
| `# lint: RULE` | its own line |
| `# lint: RULE-begin` … `# lint: RULE-end` | the lines between, inclusive |
| `# lint: RULE-file` | the whole file |

Write the reason after the rule name. A `-begin` with no `-end` runs to the end of the file.
`ratchet!` logs how many sites each rule's opt-outs removed.

## JET

[`@call_sites`](@ref) and [`@opt_sites`](@ref) turn `JET.@report_call` and `JET.@report_opt` reports
into sites. Each report becomes one site keyed by scope, function and report kind.

```julia
sites = Site[]
@call_sites "parse" sites target_modules = (MyPackage,) MyPackage.parse("1 + 2")
ratchet!(REPO, "jet", sites)
```

## Float32 code paths

A wrapper number type catches Float64 only when it is promoted with a wrapped number. A dependency
that computes at Float64 internally and narrows before returning stays invisible to it.
[`float64_ops`](@ref) reads the optimized IR of one call and counts Float64 operations:

```julia
@test float64_ops(my_kernel, (Float32, Vector{Float32})) == 0
```

Keep a positive control, a function that does use Float64, so a change to the IR filter cannot
disarm the check.

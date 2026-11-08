# Guide

## Where to run the rules

Run the rules with [`corset check`](cli.md) in a CI job of their own. The CLI page's
[recipe](cli.md#Corset-as-a-test-dependency) works when Corset is only a test dependency.

Don't run the rules inside `Pkg.test`:

- **Coverage.** CI usually runs `Pkg.test` with `--code-coverage`, which blocks inlining and constant
  folding. The typed rules (`unstable-variable`, `runtime-dispatch`, `unstable-return` and the others that
  read `entry_frames`) would then read code users never run. `entry_frames` warns once when it runs
  under coverage.
- **Shared state.** The rules would see whatever the earlier test files loaded, defined or compiled,
  so their results could depend on which tests ran and in what order.
- **Mixed failures.** A rule's failure would show up as a failing test beside the package's real ones.

`corset check` loads the package in a process of its own, without coverage.

## The pieces

A **rule** is a function from code to a vector of [`Site`](@ref)s. A site has a `key` (the name of
the offender, such as `"src/Demo.jl total"`), a file, a line and a `detail` (what the offender is, such as
``local `x`::Any``; `""` when the key says it all). The log of a failing rule prints each key's details.

A **[`Repository`](@ref)** is the tree the rules read, plus the settings that relax them.

[`offenders!`](@ref)`(repo, "rule-name", sites)` holds the sites to the repository's allowances,
logs the ones it doesn't allow and returns their keys. The rule name names the rule's table in the
baseline file and the rule in opt-out comments.

There are two kinds of rules.

- **Module rules** read a loaded module: `hidden_inputs(repo, MyPackage)`, `impure_anon_funs(repo, MyPackage)`,
  `unstable_variables(repo, entry_frames(SIGNATURES, MyPackage))`.
- **Source rules** read a file's syntax. Parse each file once with `Corset.Source`, then hand it to
  each rule: `nothing_returns(Corset.Source(REPO, file))`. `repository_sources(repo, ("src",))`
  lists a repository's files.

```julia
files = repository_sources(REPO, ("src",))
offenders!(REPO, "nothing-return", [site for file in files for site in nothing_returns(Corset.Source(REPO, file))])
```

## Adopting Corset on an existing package

Turning on a rule in a mature package usually reports hundreds of offenders. A **baseline** makes
that adoptable. It allows today's offenders and fails on new ones. Name the file in `Project.toml`:

```toml
[preferences.Corset]
baseline = "code_baseline.toml"
```

Run `corset baseline` to seed it with each rule's current offenders:

```toml
[hidden-input]
"COUNTER" = 1

[unstable-variable]
"src/Demo.jl total" = 1
```

Each entry is a key and an allowance. An integer allows that many sites under the key. A string,
such as `"kept: hot loop"`, is a note that allows any number.

After that:

- A **new** offender fails `corset check`, because its key has no entry or the entry's count is exceeded.
- A **fixed** offender lowers the file at the next `corset baseline`. An entry with
  fewer sites than it allows falls to the new count, or is deleted at zero, and the file is rewritten.
  Commit the change. The allowance can only shrink. A note stays when its offender has no site left:
  the run logs it as stale, and you delete it by hand.

## Exemptions

Settings in `[preferences.Corset]` relax rules for a whole project:

```toml
[preferences.Corset]
one_letter_exempt = ["p"]
skipped_directories = ["vendor"]
```

`one_letter_exempt` lists variable names the one-letter rule allows besides `_`. A project's own
convention, such as an argument everywhere named `p`, goes here. `skipped_directories` lists
directory names that Corset leaves out wherever they sit. Hidden directories are always left out.
The [CLI page](cli.md#Configuration) lists every setting.

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
`offenders!` logs how many sites each rule's opt-outs removed.

## JET

[`@call_sites`](@ref) and [`@opt_sites`](@ref) turn `JET.@report_call` and `JET.@report_opt` reports
into sites. Each report becomes one site keyed by scope, function and report kind.

```julia
sites = Site[]
@call_sites "parse" sites target_modules = (MyPackage,) MyPackage.parse("1 + 2")
offenders!(REPO, "jet", sites)
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

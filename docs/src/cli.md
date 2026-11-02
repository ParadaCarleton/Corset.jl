# Command-Line Interface

`corset` is the command-line tool for Corset.jl. It runs code-quality rules over a project's
source and loaded package, judges findings against a baseline, prints formatted output, and
optionally fixes or previews automated code rewrites.

## Installation

Install `corset` using Julia's declarative application manager (Julia 1.13):

```julia
pkg> app add Corset
```

You can also run it via `julia -m Corset`:

```bash
julia --project -m Corset check
```

## Commands

### `corset check`

Run the configured rules over a project.

```bash
corset check [path] [options]
```

`path` defaults to `.` (the current directory) and finds the project root at or above that path.

#### Options

- `--format <format>`: Output format (`human`, `concise`, or `json`). Default is `human`.
- `--fix`: Rewrite files in place for rules that provide an automated fixer (such as `where-return` and `misplaced-import`).
- `--diff`: Print a unified diff of the changes `--fix` would make without modifying any files on disk. Exits with code `1` if changes are detected, `0` if clean. Cannot be combined with `--fix`.
- `--pedantic`: Enable rules in the `:pedantic` group in addition to `:default` rules.
- `--deny-warnings`: Exit nonzero on warnings in addition to deny-level findings.
- `--update-baseline`: Seed missing baseline entries and lower counts for improved sites.
- `--no-load`: Skip loading the package module into Julia; runs only file and tree syntax rules.
- `--candidate-limit <count>`: The most candidate methods one runtime-dispatch site lists; `0` lists none. Overrides `candidate_limit`.
- `--entries <sources>`: Where the typed rules (`abstract-local`, `bang`, `runtime-dispatch`, `unmarked-mutation`, `widened-return`, `float-widening`) get their entry signatures, as a comma-separated list. `workload` (the default) takes the specializations the package's precompile workload compiled and the methods whose declared signature is already concrete. `tests` runs the package's tests under `--trace-compile` and keeps the traced signatures of the package's methods. `none` skips the typed rules. The command prints how many signatures each source gave and how many the walk inferred.
- `--allow <rule>`: Disable the specified rule (repeatable).
- `--warn <rule>`: Set the specified rule to warn (repeatable).
- `--deny <rule>`: Set the specified rule to deny (repeatable).

### `corset rules`

List all available rules, their group (`default` or `pedantic`), their configured level (`allow`, `warn`, or `deny`), and a one-line summary.

```bash
corset rules [path] [--pedantic]
```

## Configuration

Settings are configured per-project in the `[preferences.Corset]` table of `Project.toml`, and can be overridden locally in `LocalPreferences.toml` under `[Corset]`.

```toml
[preferences.Corset]
directories = ["src"]
baseline = "code_baseline.toml"
pedantic = false
skipped_directories = ["vendor"]
one_letter_exempt = ["p", "x"]
candidate_limit = 4
entry_points = "test/entry_points.jl:signatures"

[preferences.Corset.levels]
float64 = "deny"
where-return = "allow"
```

Keys:

- `directories`: Folders containing Julia source code to check (default: `["src"]`).
- `baseline`: Path to the baseline TOML file, relative to the project root.
- `pedantic`: Boolean to enable all pedantic rules by default.
- `skipped_directories`: Directory names omitted wherever they sit.
- `one_letter_exempt`: Variable names exempt from the `one-letter` rule.
- `candidate_limit`: The most methods `unmarked-mutation` and `float-widening` list at one runtime-dispatch site (default: `4`; `0` lists none). A site with more methods keeps its conservative report. The budget is a count, so the findings do not depend on timing.
- `entry_points`: `"file.jl:function"`, a file relative to the project root and a function in it that takes no arguments and returns a vector of signature types (`Type[Tuple{typeof(MyPackage.f), Int}]`). Its signatures replace the `--entries` sources.
- `levels`: Map of rule names to `:allow`, `:warn`, or `:deny`.

## Exit codes

- `0`: Clean run (no deny-level findings, or no findings when `--deny-warnings` is set).
- `1`: One or more findings failed the run, or `--diff` detected rewrites.
- `2`: Usage error, invalid configuration, or execution failure.

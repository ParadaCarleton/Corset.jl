# The `corset` command: parse arguments, run the rules over a project, print findings, set the exit code.
# A rule that reads the loaded package needs the project's own environment, so the command replaces
# itself with a Julia process running there (`execv`, so no launcher stays resident).

# JSON loads on first use of `--format json`, so the other formats do not pay for it.
using ArgParse: ArgParseSettings, ArgParseError, add_arg_table!, parse_args
using .Entries: Entries

const INNER_VARIABLE = "CORSET_INNER"

"""Rethrow an ArgParse error so `run_command` catches it and exits with 2."""
rethrow_arg_error(::ArgParseSettings, err::ArgParseError)::Nothing = throw(err) # lint: jet  ArgParse's error handler rethrows by design

"""Add the argument or option `name` to `settings` with the ArgParse `options` (`help`, `action`, `default`, ...)."""
option!(settings::ArgParseSettings, name::AbstractString; options...)::Nothing = (
    add_arg_table!(settings, name, Dict{Symbol, Any}(options));
    nothing
)

"""The command's argument table."""
function argument_settings()::ArgParseSettings
    settings::ArgParseSettings = ArgParseSettings(;
        prog = "corset",
        description = "Code-quality rules for Julia packages.",
        add_version = true,
        version = string(pkgversion(@__MODULE__)),
        exc_handler = rethrow_arg_error,
    )
    option!(settings, "check"; help = "run the rules over a project", action = :command)
    option!(
        settings,
        "baseline";
        help = "seed the baseline file with the rules' current offenders and lower it where they fell",
        action = :command,
    )
    option!(
        settings,
        "rules";
        help = "list the rules, their groups and their levels",
        action = :command,
    )
    for command in ("check", "baseline", "rules")
        option!(
            settings[command],
            "path";
            help = "a directory inside the project",
            default = ".",
        )
        option!(
            settings[command],
            "--pedantic";
            help = "turn on the pedantic group",
            action = :store_true,
        )
    end
    check::ArgParseSettings = settings["check"]
    option!(
        check,
        "--format";
        help = "output format: human, concise or json (default: human)",
        range_tester = in(("human", "concise", "json")),
    )
    option!(
        check,
        "--fix";
        help = "rewrite files for the rules that have a fixer",
        action = :store_true,
    )
    option!(
        check,
        "--diff";
        help = "print the changes --fix would make, write nothing, and exit 1 if there are any",
        action = :store_true,
    )
    option!(
        check,
        "--deny-warnings";
        help = "exit nonzero on warnings, not only on deny-level findings",
        action = :store_true,
    )
    for command in ("check", "baseline")
        run_options!(settings[command])
    end
    return settings
end

"""Add to `settings` the options `corset check` and `corset baseline` share: which rules run, and how."""
function run_options!(settings::ArgParseSettings)::Nothing
    option!(
        settings,
        "--no-load";
        help = "do not load the package; skip the rules that read it",
        action = :store_true,
    )
    option!(
        settings,
        "--candidate-limit";
        help = "the most methods one runtime-dispatch site lists; 0 lists none (default: the config's, else $DEFAULT_CANDIDATE_LIMIT)",
        arg_type = Int,
    )
    option!(
        settings,
        "--entries";
        help = "where the typed rules' entry signatures come from, comma-separated: workload (compiled specializations and concrete declarations), tests (run the tests under --trace-compile) or none (default: workload)",
    )
    option!(settings, "--allow"; help = "turn a rule off (repeatable)", action = :append_arg)
    option!(settings, "--warn"; help = "set a rule to warn (repeatable)", action = :append_arg)
    option!(settings, "--deny"; help = "set a rule to deny (repeatable)", action = :append_arg)
    return nothing
end

"""The directory of the project that contains `path`."""
function project_root(path::AbstractString)::String
    project = Base.current_project(abspath(path))
    if isnothing(project)
        throw(UsageError("no Project.toml found at or above $(abspath(path))"))
    end
    return dirname(project)
end

"""
`config` with the pedantic group switched on when `pedantic` is set, the levels in `overrides` (rule => level)
applied, and `candidate_limit` set unless it is `nothing`.
"""
function with_overrides(
        config::Config,
        pedantic::Bool,
        overrides::AbstractVector{<:Pair{String, Symbol}},
        candidate_limit::Union{Nothing, Integer},
    )::Config
    levels::Dict{String, Symbol} = merge(config.levels, Dict{String, Symbol}(overrides))
    unknown::Vector{String} = sort!(setdiff(collect(keys(levels)), collect(rule_name.(RULES))))
    if !isempty(unknown)
        throw(UsageError("no such rule: $(join(unknown, ", ")); `corset rules` lists them"))
    end
    return Config(
        config.directories,
        config.baseline,
        config.one_letter_exempt,
        config.skipped_directories,
        config.pedantic || pedantic,
        levels,
        checked_limit(something(candidate_limit, config.candidate_limit), "--candidate-limit"),
        config.entry_points,
        config.file_line_limit,
        config.struct_field_limit,
        config.strict_captures,
        config.forbidden_patterns,
    )
end

"""The options of `corset rules`."""
struct RulesOptions
    path::String
    pedantic::Bool
end

"""
The options of `corset check`, as ArgParse parsed them; `overrides` are the `rule => level` pairs of
`--allow`, `--warn` and `--deny`. `corset baseline` is a check with `update_baseline` set.
"""
struct CheckOptions
    path::String
    pedantic::Bool
    format::Union{Nothing, String}
    fix::Bool
    diff::Bool
    deny_warnings::Bool
    update_baseline::Bool
    no_load::Bool
    overrides::Vector{Pair{String, Symbol}}
    candidate_limit::Union{Nothing, Int}
    entries::Union{Nothing, String}
end

"""The options of `corset check`, or of `corset baseline` when `update_baseline` is set, from its parsed `arguments`."""
function CheckOptions(arguments::AbstractDict, update_baseline::Bool)::CheckOptions
    return CheckOptions(
        arguments["path"],
        arguments["pedantic"],
        get(arguments, "format", nothing),
        get(arguments, "fix", false),
        get(arguments, "diff", false),
        get(arguments, "deny-warnings", false),
        update_baseline,
        arguments["no-load"],
        vcat(level_overrides.((arguments,), ("allow", "warn", "deny"))...),
        arguments["candidate-limit"],
        arguments["entries"],
    )
end

"""The `rule => level` pairs the option `name` (`allow`, `warn` or `deny`) of `arguments` sets."""
function level_overrides(arguments::AbstractDict, name::AbstractString)::Vector{Pair{String, Symbol}}
    level = Symbol(name)
    return Pair{String, Symbol}[rule => level for rule in something(arguments[name], String[])]
end

"""The typed options of the command ArgParse parsed into `parsed`."""
function command_options(parsed::AbstractDict)::Union{RulesOptions, CheckOptions}
    command::String = parsed["%COMMAND%"]
    if command == "rules"
        return RulesOptions(parsed["rules"]["path"], parsed["rules"]["pedantic"])
    end
    return CheckOptions(parsed[command], command == "baseline")
end

"""Whether any rule `config` leaves on reads the loaded package."""
reads_package(config::Config)::Bool = !isempty(module_rule_names(enabled_rules(config)))

"""The package at `root`, loaded in the running process."""
function load_package(root::AbstractString)::Module
    name::Union{String, Nothing} = get(TOML.parsefile(joinpath(root, "Project.toml")), "name", nothing)
    if isnothing(name)
        throw(UsageError("$root/Project.toml names no package; run with --no-load to skip the rules that read one"))
    end
    return Base.require(Main, Symbol(name))
end

"""
    relaunch(root, args)

Replace this process with a Julia process whose active project is `root`, running `corset` on `args`.
Corset's own environment stays on the load path after the project's, so the project's versions of shared
dependencies win, and the default environment (`@v#.#`) comes last, so a JET installed there runs the `jet` rule. Where `execv` does not exist the command runs as a child and its exit code is returned.
"""
function relaunch(root::AbstractString, args::AbstractVector{<:AbstractString})::Int # COV_EXCL_LINE # lint: jet  execv replaces the process, so on POSIX it leaves only by throwing when execv fails
    # COV_EXCL_START
    # execv replaces the process before it can write its coverage
    ENV[INNER_VARIABLE] = "1"
    corset_project = Base.active_project()
    if isnothing(corset_project)
        throw(UsageError("corset relaunches in the project's environment and keeps its own on the load path, but no project is active"))
    end
    ENV["JULIA_LOAD_PATH"] = join(
        ["@", dirname(corset_project), "@stdlib", "@v#.#"],
        ifelse(Sys.iswindows(), ";", ":"),
    )
    command = `$(Base.julia_cmd()) --startup-file=no --project=$root -e "using Corset; exit(Corset.main(ARGS))" -- $args`
    if Sys.iswindows()
        return run(ignorestatus(command)).exitcode
    end
    strings = collect(command.exec)
    GC.@preserve strings begin
        argv = Ptr{UInt8}[pointer.(strings); C_NULL]
        ccall(:execv, Cint, (Cstring, Ptr{Ptr{UInt8}}), strings[1], argv)
    end
    error("execv failed: $(Libc.strerror(Libc.errno()))")
    # COV_EXCL_STOP
end

"""The `Entries` sources each `--entries` name stands for."""
const ENTRY_SOURCES = (; workload = (:compiled, :declared), tests = (:tests,), none = ())

"""
The `Entries` sources the `--entries` list `entries` (`workload,tests`) names, `workload` when it is
`nothing`. An unknown name, or `none` beside another, throws.
"""
function entry_sources(entries::Union{Nothing, AbstractString})::Vector{Symbol}
    names = Symbol.(split(something(entries, "workload"), ','))
    unknown = setdiff(names, keys(ENTRY_SOURCES))
    if !isempty(unknown)
        throw(UsageError("--entries names no source $(join(unknown, ", ")); the sources are $(join(keys(ENTRY_SOURCES), ", "))"))
    end
    if :none in names && length(names) > 1
        throw(UsageError("--entries none seeds nothing; it cannot join $(join(setdiff(names, (:none,)), ", "))"))
    end
    return unique(Symbol[source for name in names for source in ENTRY_SOURCES[name]])
end

"""
The `entry_sources` of `entries`; throws when the `entry_points` of `config` are set beside them,
since those replace the sources.
"""
function checked_entries(config::Config, entries::Union{Nothing, AbstractString})::Vector{Symbol}
    if !isnothing(config.entry_points) && !isnothing(entries)
        throw(UsageError("entry_points in the configuration replaces --entries; drop one"))
    end
    return entry_sources(entries)
end

"""
The flags of `options` that `--diff`, when set, ignores, as written on the command line: it only
prints the fixers' rewrites.
"""
function diff_ignored(options::CheckOptions)::Vector{String}
    if !options.diff
        return String[]
    end
    flags = [
        "--format" => !isnothing(options.format),
        "--deny-warnings" => options.deny_warnings,
        "--entries" => !isnothing(options.entries),
        "--candidate-limit" => !isnothing(options.candidate_limit),
    ]
    return first.(filter(last, flags))
end

"""
`options`, checked under `config`: `--diff` with a flag it ignores, `--entries` with `--no-load` (the
typed rules need the package), an unknown `--entries` source, or `corset baseline` in a project that
names no baseline file throws.
"""
function checked_options(options::CheckOptions, config::Config)::CheckOptions
    if options.update_baseline && isnothing(config.baseline)
        throw(UsageError("`corset baseline` writes the file `baseline` names in [preferences.Corset] of Project.toml, and it names none"))
    end
    ignored = diff_ignored(options)
    if !isempty(ignored)
        throw(UsageError("--diff only prints the fixers' rewrites and ignores $(join(ignored, ", ")); drop them"))
    end
    if options.no_load && !isnothing(options.entries)
        throw(UsageError("--no-load skips the typed rules, which read --entries; drop one"))
    end
    checked_entries(config, options.entries)
    return options
end

"""
The entry signatures of the loaded package `mod` at `root`, by source name: the `entry_points` of
`config` alone when it sets them, else the `entries` sources, read from `mod`'s methods `own_methods`.
Test output goes to `output`; the tests run without this command's own environment variables.
"""
function seed_sources(
        config::Config,
        root::AbstractString,
        entries::Union{Nothing, AbstractString},
        mod::Module,
        output::IO;
        own_methods::AbstractVector{Method} = defined_methods(mod),
    )::Vector{Pair{String, Vector{Type}}}
    sources = checked_entries(config, entries)
    if !isnothing(config.entry_points)
        file, name = config.entry_points
        return ["entry_points" => Entries.configured_signatures(abspath(root, file), name)]
    end
    warn_tests!(output, sources)
    return Pair{String, Vector{Type}}.(string.(sources), Entries.source_signatures.((mod,), sources; root, output, unset = (INNER_VARIABLE, "JULIA_LOAD_PATH"), own_methods))
end

"""Print to `output` that the `:tests` source, when `sources` holds it, runs the whole test suite and its child processes."""
function warn_tests!(output::IO, sources::AbstractVector{Symbol})::Nothing
    if :tests in sources
        println(output, "warning: --entries tests runs the package's whole test suite, and every process it starts, beside this one")
    end
    return nothing
end

"""
The line that says how many signatures each of `sources` gave, how many seeds their union holds, how
many of the package's frames the walk kept (`frames`), and the process's peak resident memory `peak` in bytes.
"""
function seed_summary(sources::AbstractVector{<:Pair{String, <:AbstractVector{<:Type}}}, frames::AbstractVector{Inferred}, peak::Integer)::String
    counts = join(["$name $(length(signatures))" for (name, signatures) in sources], ", ")
    seeds = length(unique(collect(Type, Iterators.flatten(last.(sources)))))
    return "entry signatures: $counts; $seeds seeds, $(length(frames)) frames kept; peak RSS $(peak ÷ 2^20) MiB"
end

"""The `entry_frames` of `mod` the typed rules read, walked once from the union of `sources`."""
seeded_frames(sources::AbstractVector{<:Pair{String, <:AbstractVector{<:Type}}}, mod::Module)::Vector{Inferred} =
    entry_frames(unique(collect(Type, Iterators.flatten(last.(sources)))), mod)

"""The path of `site` relative to `root`; empty for a site with no file."""
function display_path(root::AbstractString, site::Site)::String
    if isempty(site.file)
        return ""
    end
    return relpath(site.file, root)
end

"""The ` (detail)` a concise finding line ends with; empty for a site with no detail."""
function detail_note(detail::AbstractString)::String
    if isempty(detail)
        return ""
    end
    return " ($detail)"
end

"""Print `findings` to `io` in `format` (human, concise or json)."""
function print_findings(
        io::IO,
        root::AbstractString,
        findings::AbstractVector{F},
        format::AbstractString,
    )::Nothing where {F <: Finding}
    if format == "json"
        records = [
            (;
                rule = finding.rule, level = finding.level, key = finding.site.key, file = display_path(
                    root,
                    finding.site,
                ), line = finding.site.line, detail = finding.site.detail,
            )
                for finding in findings
        ]
        json::Module = Base.require(@__MODULE__, :JSON)
        println(io, Base.invokelatest(json.json, records))
        return nothing
    end
    for finding in findings
        place = display_path(root, finding.site)
        if format == "concise"
            println(
                io,
                "$place:$(finding.site.line): $(finding.level): [$(finding.rule)] $(finding.site.key)" * detail_note(finding.site.detail),
            )
        else
            println(io, "$(finding.level)[$(finding.rule)]: $(finding.site.key)")
            if !isempty(place)
                println(io, "  --> $place:$(finding.site.line)")
            end
            if !isempty(finding.site.detail)
                println(io, "  = $(finding.site.detail)")
            end
        end
    end
    return nothing
end

"""The exit code for `findings`: 1 for any deny-level finding, or any finding when `deny_warnings`; else 0."""
function exit_code(findings::AbstractVector{Finding}, deny_warnings::Bool)::Int
    return Int(any(finding -> finding.level === :deny || deny_warnings, findings))
end

"""The `corset rules` line for `rule`: its name, group, the level `config` gives it, and its summary."""
rule_line(config::Config, rule::Rule)::String = rpad(rule_name(rule), NAME_COLUMN) * rpad(rule_group(rule), 10) * rpad(level(config, rule), 7) * rule_summary(rule)

"""The width of the name column of `corset rules`: the longest rule name and a space."""
const NAME_COLUMN = maximum(length ∘ rule_name, RULES) + 1

"""`corset rules`: one line per rule with its group and the level `config` gives it."""
function print_rules(io::IO, config::Config)::Nothing
    println(io, join(rule_line.((config,), RULES), "\n"))
    return nothing
end

"""`corset check --diff`: print the changes `--fix` would make to `io`; the exit code is 1 when there are any."""
function print_fix_diff(io::IO, config::Config, root::AbstractString, fix::Bool)::Int # COV_EXCL_LINE
    if fix
        throw(UsageError("--diff writes nothing and --fix writes the changes; pass one"))
    end
    changes = fix_diff(config, root)
    print(io, changes)
    return Int(!isempty(changes))
end

"""Run `corset check`, or `corset baseline`, with `options` (from the command line `args`); returns the exit code."""
function run_options(options::CheckOptions, args::AbstractVector{<:AbstractString}, out::IO, err::IO)::Int
    root = project_root(options.path)
    config = with_overrides(load_config(root), options.pedantic, options.overrides, options.candidate_limit)
    options = checked_options(options, config)
    if options.diff
        return print_fix_diff(out, config, root, options.fix)
    end
    loads = reads_package(config) && !options.no_load
    if loads && !haskey(ENV, INNER_VARIABLE)
        return relaunch(root, args) # COV_EXCL_LINE
    end
    mod = nothing
    own_methods = Method[]
    frames = nothing
    sources = Pair{String, Vector{Type}}[]
    if loads
        mod = load_package(root)
        own_methods = defined_methods(mod)
        if any(reads_signatures, enabled_rules(config))::Bool
            sources = seed_sources(config, root, options.entries, mod, err; own_methods)
        end
        if !isempty(sources)
            frames = seeded_frames(sources, mod)
        end
    end
    findings, skipped = run_rules(config, root; mod, frames, fix = options.fix, update_baseline = options.update_baseline, own_methods)
    print_findings(out, root, findings, something(options.format, "human"))
    if !isnothing(frames)
        println(err, seed_summary(sources, frames, Sys.maxrss()))
    end
    if !isempty(skipped)
        println(err, "skipped (they read the loaded package, need entry signatures, or need JET installed): ", join(skipped, ", "))
    end
    return exit_code(findings, options.deny_warnings)
end

"""
    check_project(root, mod, signatures; out = stdout, format = "human", deny_warnings = false, update_baseline = false)

`corset check` for a package `mod` already loaded in this process, the entry `signatures` given by the
caller, and the configuration of the project at `root`. Prints the findings to `out` and returns the exit
code: a test calls this once, `@test check_project(root, MyPackage, signatures) == 0`. `update_baseline`
seeds and lowers the baseline file as `corset baseline` does.
"""
function check_project(
        root::AbstractString,
        mod::Module,
        signatures::AbstractVector{<:Type};
        out::IO = stdout,
        format::AbstractString = "human",
        deny_warnings::Bool = false,
        update_baseline::Bool = false,
    )::Int
    project = project_root(root)
    config = load_config(project)
    frames = nothing
    if any(reads_signatures, enabled_rules(config))::Bool
        frames = seeded_frames(Pair{String, Vector{Type}}["signatures" => Type[signatures...]], mod)
    end
    findings, _ = run_rules(config, project; mod, frames, update_baseline)
    print_findings(out, project, findings, format)
    return exit_code(findings, deny_warnings)
end

"""Run `corset rules`: print the rules and their levels to `out`."""
function run_options(options::RulesOptions, args::AbstractVector{<:AbstractString}, out::IO, err::IO)::Int
    config = with_overrides(load_config(project_root(options.path)), options.pedantic, Pair{String, Symbol}[], nothing)
    print_rules(out, config)
    return 0
end

"""Whether `error_` is a write to a closed pipe (`corset rules | head`), which ends the run quietly."""
broken_pipe(error_::Any)::Bool = error_ isa Base.IOError && error_.code == Base.UV_EPIPE

"""The message `corset` prints for a usage or configuration error."""
error_message(error_::Union{UsageError, Entries.SourceError})::String = error_.msg
error_message(error_::ArgParseError)::String = error_.text
error_message(error_::TOML.ParserError)::String = sprint(showerror, error_)

"""
    run_command(args, out, err)

The `corset` command on the streams `out` and `err`. Returns the exit code: 0 when clean, 1 when a
finding fails the run, 2 on a usage or configuration error (`UsageError`, `Entries.SourceError`, a bad
argument or a malformed TOML file), 3 on any other exception, which is Corset's own failure (its error
and backtrace go to `err`). An interrupt is rethrown.
"""
function run_command(args::AbstractVector{<:AbstractString}, out::IO, err::IO)::Int
    try
        return run_options(command_options(parse_args(collect(String, args), argument_settings())), args, out, err)
    catch error_
        if broken_pipe(error_)
            return 0
        elseif error_ isa Union{UsageError, Entries.SourceError, ArgParseError, TOML.ParserError}
            println(err, "corset: ", error_message(error_))
            return 2
        elseif error_ isa InterruptException
            rethrow()
        end
        println(err, "corset: internal error: ", sprint(showerror, error_, catch_backtrace())) # lint: runtime-dispatch  any exception
        return 3
    end
end

"""`run_command` on the process's standard streams, as they are when the command starts."""
(@main)(args::AbstractVector{<:AbstractString})::Int = run_command(args, stdout, stderr)

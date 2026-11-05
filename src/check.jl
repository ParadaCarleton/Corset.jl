# Runs the registered rules over a project and judges their sites against the baseline.

using diffutils_jll: diffutils_jll

"""The allowances the baseline file of `repository` holds for `rule`: none when there is no file or no table."""
function allowances(repository::Repository, rule::AbstractString)::Dict{String, Union{Int, String}}
    if isnothing(repository.baseline) || !isfile(repository.baseline)
        return Dict{String, Union{Int, String}}()
    end
    return get(read_baseline(repository.baseline), rule, Dict{String, Union{Int, String}}())
end

"""The keys of `kept` sites that the baseline of `repository` does not allow for `rule`; with `update`, it is seeded and lowered as `offenders!` does."""
function disallowed_keys(
        repository::Repository,
        rule::AbstractString,
        sites::AbstractVector{Site},
        kept::AbstractVector{Site},
        update::Bool,
        comments::AbstractDict{String, Vector{OptOutComment}},
    )::Vector{String}
    if update
        if !isnothing(repository.baseline) && !isfile(repository.baseline)
            mkpath(dirname(repository.baseline))
            touch(repository.baseline)
        end
        return offenders!(repository, rule, sites; comments, seed = true)
    end
    return exceeding(allowances(repository, rule), tally(kept))
end

"""
The findings among `sites` of `rule` at `level`: the sites no `# lint:` comment opts out, whose key the
baseline does not allow. With `update`, the baseline is seeded and lowered as `offenders!` does.
`comments` holds the `# lint:` comments of the files already parsed; any other file is read.
"""
function judge(
        repository::Repository,
        rule::Rule,
        level::Symbol,
        sites::AbstractVector{Site},
        update::Bool,
        comments::AbstractDict{String, Vector{OptOutComment}},
    )::Vector{Finding}
    name::String = rule_name(rule)
    kept, _ = unopted(sites, name, comments)
    over = disallowed_keys(repository, name, sites, kept, update, comments)
    return Finding.(name, level, kept[in.(getfield.(kept, :key), (over,))])
end

"""Whether `rule` reads the frames inference gives the entry signatures (`entry_frames`)."""
reads_signatures(rule::Rule)::Bool = rule isa Union{AbstractLocalRule, BangRule, UnmarkedMutationRule, RuntimeDispatchRule, WidenedReturnRule, FloatWideningRule, RecursionLimitRule, JetRule}

"""
Whether `rule` has what it reads: the loaded package `mod` for a module rule, `frames` for a rule that
reads inferred types, and JET on the load path for the `jet` rule.
"""
can_run(rule::Rule, mod::Union{Module, Nothing}, frames::Union{AbstractVector{Inferred}, Nothing})::Bool =
    (!(rule isa ModuleRule) || !isnothing(mod)) && (!reads_signatures(rule) || !isnothing(frames)) && (!(rule isa JetRule) || installed(JET_ID))

"""The names of the rules in `rules` that read the loaded package."""
module_rule_names(rules::Tuple)::Vector{String} = [
    rule_name(rule)
        for rule in rules
        if rule isa ModuleRule
]

"""Whether `config` leaves `rule` on."""
is_on(config::Config, rule::Rule)::Bool = level(config, rule) !== :allow

"""The rules `config` leaves on."""
enabled_rules(config::Config)::Tuple = filter(Base.Fix1(is_on, config), RULES)

"""Run the fixer of every fixable rule in `rules` over the files under `directories` of `repository`."""
apply_fixes!(::Tuple{}, ::Repository, ::Tuple{Vararg{String}})::Nothing = nothing

function apply_fixes!(rules::Tuple, repository::Repository, directories::Tuple{Vararg{String}})::Nothing
    apply_fix!(first(rules), repository, directories)
    return apply_fixes!(Base.tail(rules), repository, directories)
end

"""Run the fixer of `rule` over the files under `directories` of `repository`, when `rule` has one."""
function apply_fix!(rule::Rule, repository::Repository, directories::Tuple{Vararg{String}})::Nothing
    if fixable(rule)
        fix!(rule, repository, directories)
    end
    return nothing
end

"""The unified diff from the file `before` to the file `after`, labeled `label`; empty when they match."""
function file_diff(
        label::AbstractString,
        before::AbstractString,
        after::AbstractString,
    )::String
    return read(
        ignorestatus(
            `$(diffutils_jll._diff()) -u --label a/$label --label b/$label $before $after`,
        ),
        String,
    )
end

"""
    fix_diff(config, root)

The unified diff of the rewrites `--fix` would make, computed on a copy of the source directories.
The tree at `root` is not written.
"""
function fix_diff(config::Config, root::AbstractString)::String
    original = repository(config, root)
    directories = present_directories(original, config.directories)
    copies = mktempdir()
    for directory in directories
        mkpath(dirname(joinpath(copies, directory)))
        cp(joinpath(original.root, directory), joinpath(copies, directory))
    end
    apply_fixes!(enabled_rules(config), repository(config, copies), directories)
    labels = relpath.(repository_sources(original, directories), original.root)
    return join(file_diff.(labels, joinpath.(original.root, labels), joinpath.(copies, labels)))
end

"""
    run_rules(config, root; mod = nothing, frames = nothing, fix = false, update_baseline = false, own_methods = defined_methods(mod))

The findings of every rule `config` leaves on, over the project at `root`, and the names of the rules
skipped because they read the loaded package `mod` and none was given, or are `jet` and JET is not installed. The rules that read inferred types also
need `frames`, the `entry_frames` of `mod`; without them they are skipped. `fix` first rewrites the files
for the rules that have a fixer. `update_baseline` seeds and lowers the baseline file; without it the
baseline is only read. `own_methods` holds the `defined_methods` of `mod`.
"""
function run_rules( # lint: abstract-local  loops over a tuple of different rule types
        config::Config,
        root::AbstractString;
        mod::Union{Module, Nothing} = nothing,
        frames::Union{AbstractVector{Inferred}, Nothing} = nothing,
        fix::Bool = false,
        update_baseline::Bool = false,
        own_methods::AbstractVector{Method} = defined_methods(mod),
    )::Tuple{Vector{Finding}, Vector{String}}
    repository_ = repository(config, root)
    directories = present_directories(repository_, config.directories)
    enabled = enabled_rules(config)
    runnable = enabled[collect(can_run.(enabled, (mod,), (frames,)))]
    skipped = setdiff(module_rule_names(enabled), module_rule_names(runnable))
    if fix
        apply_fixes!(runnable, repository_, directories)
    end
    inferred = something(frames, Inferred[])
    context = Context(repository_, directories, mod; inferred, candidates = CandidateSearch(inferred; config.candidate_limit), own_methods)
    sites = Dict{String, Vector{Site}}(rule_name(rule) => Site[] for rule in runnable)
    for rule in runnable
        if !(rule isa FileRule)
            append!(sites[rule_name(rule)], check(rule, context))
        end
    end
    file_rules = Tuple(rule for rule in runnable if rule isa FileRule)
    if !isempty(file_rules)
        for source in context.sources
            for rule in file_rules
                append!(sites[rule_name(rule)], check(rule, context, source))
            end
        end
    end
    comments = context.comments
    findings = context.parse_errors
    for rule in runnable
        append!(
            findings,
            judge(
                repository_,
                rule,
                level(config, rule),
                sites[rule_name(rule)],
                update_baseline,
                comments,
            ),
        )
    end
    return sort!(
            findings;
            by = finding -> (finding.site.file, finding.site.line, finding.rule),
        ),
        skipped
end

# Runs the registered rules over a project and judges their sites against the baseline.

using diffutils_jll: diffutils_jll

"""One site a rule found, with the level it was found at."""
struct Finding
    rule::String
    level::Symbol
    site::Site
end

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
    )::Vector{String}
    if update
        if !isnothing(repository.baseline) && !isfile(repository.baseline)
            mkpath(dirname(repository.baseline))
            touch(repository.baseline)
        end
        return offenders!(repository, rule, sites)
    end
    return exceeding(allowances(repository, rule), tally(kept))
end

"""
The findings among `sites` of `rule` at `level`: the sites no `# lint:` comment opts out, whose key the
baseline does not allow. With `update`, the baseline is seeded and lowered as `offenders!` does.
"""
function judge(
        repository::Repository,
        rule::Rule,
        level::Symbol,
        sites::AbstractVector{Site},
        update::Bool,
    )::Vector{Finding}
    name::String = rule_name(rule)
    kept, _ = unopted(sites, name)
    over = disallowed_keys(repository, name, sites, kept, update)
    return Finding.(name, level, kept[in.(getfield.(kept, :key), (over,))])
end

"""Whether `rule` reads the types inference gives `signatures` (`inferred_methods`)."""
reads_signatures(rule::Rule)::Bool = rule isa Union{AbstractLocalRule, BangRule, UnmarkedMutationRule}

"""Whether `rule` has what it reads: the loaded package `mod` for a module rule, `signatures` for a rule that reads inferred types."""
can_run(rule::Rule, mod::Union{Module, Nothing}, signatures::Union{AbstractVector{<:Type}, Nothing})::Bool =
    (!(rule isa ModuleRule) || !isnothing(mod)) && (!reads_signatures(rule) || !isnothing(signatures))

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

"""Run the fixer of every fixable rule in `rules` over the files `context` names."""
apply_fixes!(::Tuple{}, ::Context)::Nothing = nothing

function apply_fixes!(rules::Tuple, context::Context)::Nothing
    apply_fix!(first(rules), context)
    return apply_fixes!(Base.tail(rules), context)
end

"""Run the fixer of `rule` over the files `context` names, when `rule` has one."""
function apply_fix!(rule::Rule, context::Context)::Nothing
    if fixable(rule)
        fix!(rule, context)
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
        cp(joinpath(original.root, directory), joinpath(copies, directory))
    end
    apply_fixes!(
        enabled_rules(config),
        Context(repository(config, copies), directories, nothing, Inferred[]),
    )
    labels = relpath.(repository_sources(original, directories), original.root)
    return join(file_diff.(labels, joinpath.(original.root, labels), joinpath.(copies, labels)))
end

"""
    run_rules(config, root; mod = nothing, signatures = nothing, fix = false, update_baseline = false)

The findings of every rule `config` leaves on, over the project at `root`, and the names of the rules
skipped because they read the loaded package `mod` and none was given. `abstract-local` and `bang` also
need `signatures`, the fixed workload `inferred_methods` types `mod` over; without them they are skipped. `fix` first rewrites the files
for the rules that have a fixer. `update_baseline` seeds and lowers the baseline file; without it the
baseline is only read.
"""
function run_rules( # lint: abstract-local  loops over a tuple of different rule types
        config::Config,
        root::AbstractString;
        mod::Union{Module, Nothing} = nothing,
        signatures::Union{AbstractVector{<:Type}, Nothing} = nothing,
        fix::Bool = false,
        update_baseline::Bool = false,
    )::Tuple{Vector{Finding}, Vector{String}}
    repository_ = repository(config, root)
    directories = present_directories(repository_, config.directories)
    enabled = enabled_rules(config)
    runnable = enabled[collect(can_run.(enabled, (mod,), (signatures,)))]
    skipped = setdiff(module_rule_names(enabled), module_rule_names(runnable))
    if fix
        apply_fixes!(runnable, Context(repository_, directories, mod, Inferred[]))
    end
    inferred = Inferred[]
    if any(reads_signatures, runnable)
        inferred = inferred_methods(mod, signatures)
    end
    context = Context(repository_, directories, mod, inferred)
    sites = Dict{String, Vector{Site}}(rule_name(rule) => Site[] for rule in runnable)
    for rule in runnable
        if !(rule isa FileRule)
            append!(sites[rule_name(rule)], check(rule, context))
        end
    end
    file_rules = Tuple(rule for rule in runnable if rule isa FileRule)
    if !isempty(file_rules)
        for path in repository_sources(repository_, directories)
            located = located_source(path)
            for rule in file_rules
                append!(sites[rule_name(rule)], check(rule, context, path, located))
            end
        end
    end
    findings = Finding[]
    for rule in runnable
        append!(
            findings,
            judge(
                repository_,
                rule,
                level(config, rule),
                sites[rule_name(rule)],
                update_baseline,
            ),
        )
    end
    return sort!(
            findings;
            by = finding -> (finding.site.file, finding.site.line, finding.rule),
        ),
        skipped
end

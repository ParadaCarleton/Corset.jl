# Per-project settings for the `corset` command, read from the `[preferences.Corset]` table of the
# project's Project.toml and the `[Corset]` table of its LocalPreferences.toml (which wins per key).

using Configurations: @option, from_dict, FieldTypeConversionError, InvalidKeyError

"""
    Config

What a project sets for `corset`: the source `directories` to read, the `baseline` file, the
`Repository` exemptions, whether the `pedantic` group is on, and per-rule `levels` (`:allow`,
`:warn` or `:deny`) that override a rule's group.
"""
struct Config
    directories::Tuple{Vararg{String}}
    baseline::Union{String, Nothing}
    one_letter_exempt::Tuple{Vararg{Symbol}}
    skipped_directories::Tuple{Vararg{String}}
    pedantic::Bool
    levels::Dict{String, Symbol}
end

const LEVELS = (:allow, :warn, :deny)

"""One `[Corset]` preferences table, as written: a key left out is `nothing`, so a layer overlays another key by key."""
@option struct Preferences
    directories::Union{Nothing, Vector{String}} = nothing
    baseline::Union{Nothing, String} = nothing
    one_letter_exempt::Union{Nothing, Vector{String}} = nothing
    skipped_directories::Union{Nothing, Vector{String}} = nothing
    pedantic::Union{Nothing, Bool} = nothing
    levels::Union{Nothing, Dict{String, String}} = nothing
end

"""Merge two preference dictionaries, with `over` overriding matching keys in `under`."""
merged(under::Dict, over::Dict)::Dict = merge(under, over)
merged(under::Any, over::Any)::Any = something(over, under, Some(nothing))

"""`over`'s keys where it sets them, else `under`'s; nested dictionaries are merged."""
overlay(under::Preferences, over::Preferences)::Preferences = Preferences(
    merged.(getfield.((under,), fieldnames(Preferences)), getfield.((over,), fieldnames(Preferences)))...
)

"""The preferences in the TOML `file` below the `path` of table names (`("preferences", "Corset")`); none set when there is no file or table."""
function read_preferences(file::AbstractString, path::Tuple{Vararg{String}})::Preferences # lint: abstract-local  TOML tables are Dict{String, Any}
    if !isfile(file)
        return Preferences()
    end
    table = TOML.parsefile(file)
    for name in path
        table = get(table, name, Dict{String, Any}())
    end
    try
        return from_dict(Preferences, table)
    catch error_
        if error_ isa Union{InvalidKeyError, FieldTypeConversionError}
            error("[$(join(path, "."))] in $file: $(sprint(showerror, error_))")
        end
        rethrow() # COV_EXCL_LINE
    end
end

"""
    load_config(root)

The `Config` of the project at `root`: the `[preferences.Corset]` table of its Project.toml overlaid by
the `[Corset]` table of its LocalPreferences.toml, key by key. An unknown key, an unknown rule name or a
level other than `allow`, `warn` or `deny` throws, so a typo cannot silently switch a rule off.
"""
function load_config(root::AbstractString)::Config
    prefs = overlay(
        read_preferences(joinpath(root, "Project.toml"), ("preferences", "Corset")),
        read_preferences(joinpath(root, "LocalPreferences.toml"), ("Corset",)),
    )
    levels = Dict{String, Symbol}(
        rule => Symbol(level)
            for (rule, level) in something(prefs.levels, Dict{String, String}())
    )
    for (rule, level) in levels
        if rule ∉ rule_name.(RULES)
            error(
                "[preferences.Corset.levels] names no rule $(repr(rule)); the rules are $(join(rule_name.(RULES), ", "))",
            )
        end
        if level ∉ LEVELS
            error(
                "[preferences.Corset.levels] sets $rule to $(repr(string(level))); a level is one of $(join(LEVELS, ", "))",
            )
        end
    end
    return Config(
        Tuple(something(prefs.directories, ["src"])),
        prefs.baseline,
        Tuple(Symbol.(something(prefs.one_letter_exempt, String[]))),
        Tuple(something(prefs.skipped_directories, String[])),
        something(prefs.pedantic, false),
        levels,
    )
end

"""The `Repository` for `config` rooted at `root`; a relative baseline path is taken from `root`."""
function repository(config::Config, root::AbstractString)::Repository
    baseline = nothing
    if !isnothing(config.baseline)
        baseline = abspath(root, config.baseline)
    end
    return Repository(
        root;
        baseline,
        one_letter_exempt = config.one_letter_exempt,
        skipped_directories = config.skipped_directories,
    )
end

"""The level `config` gives `rule`: its own setting, else `:warn` for the default group and for the pedantic group when on."""
function level(config::Config, rule::Rule)::Symbol
    if haskey(config.levels, rule_name(rule))
        return config.levels[rule_name(rule)]
    end
    return ifelse(rule_group(rule) === :default || config.pedantic, :warn, :allow)
end

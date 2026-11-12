# Per-project settings for the `corset` command, read from the `[preferences.Corset]` table of the
# project's Project.toml and the `[Corset]` table of its LocalPreferences.toml (which wins per key).

using Configurations: @option, from_dict, FieldTypeConversionError, InvalidKeyError

"""
    Config

What a project sets for `corset`: the source `directories` to read, the `baseline` file, the
`Repository` exemptions, whether the `pedantic` group is on, and per-rule `levels` (`:allow`,
`:warn` or `:deny`) that override a rule's group, the `candidate_limit` of the typed rules'
`CandidateSearch`, the `file_line_limit` of the `file-length` rule, and the `entry_points` (`file => function`, the file relative to the project) whose
signatures replace the `--entries` sources.
"""
struct Config
    directories::Tuple{Vararg{String}}
    baseline::Union{String, Nothing}
    one_letter_exempt::Tuple{Vararg{Symbol}}
    skipped_directories::Tuple{Vararg{String}}
    pedantic::Bool
    levels::Dict{String, Symbol}
    candidate_limit::Int
    entry_points::Union{Nothing, Pair{String, Symbol}}
    file_line_limit::Int
    struct_field_limit::Int
    strict_captures::Bool
    forbidden_patterns::Tuple{Vararg{ForbiddenPattern}}
    banned_words::Tuple{Vararg{String}}
    banned_suffixes::Tuple{Vararg{String}}
end

const LEVELS = (:allow, :warn, :deny)

"""One `[[preferences.Corset.forbidden_patterns]]` entry, as written (`ForbiddenPattern` holds the compiled form)."""
@option struct ForbiddenPatternPreference
    name::String # COV_EXCL_LINE  a constructor `@option` generates, attributed to this line
    pattern::String
    message::String
    unless::Union{Nothing, String} = nothing
    skip_files::Vector{String} = String[]
end

"""One `[Corset]` preferences table, as written: a key left out is `nothing`, so a layer overlays another key by key."""
@option struct Preferences
    directories::Union{Nothing, Vector{String}} = nothing
    baseline::Union{Nothing, String} = nothing
    one_letter_exempt::Union{Nothing, Vector{String}} = nothing
    skipped_directories::Union{Nothing, Vector{String}} = nothing
    pedantic::Union{Nothing, Bool} = nothing
    levels::Union{Nothing, Dict{String, String}} = nothing
    candidate_limit::Union{Nothing, Int} = nothing
    entry_points::Union{Nothing, String} = nothing
    file_line_limit::Union{Nothing, Int} = nothing
    struct_field_limit::Union{Nothing, Int} = nothing
    strict_captures::Union{Nothing, Bool} = nothing
    forbidden_patterns::Union{Nothing, Vector{ForbiddenPatternPreference}} = nothing
    banned_words::Union{Nothing, Vector{String}} = nothing
    banned_suffixes::Union{Nothing, Vector{String}} = nothing
end

"""Merge two preference dictionaries, with `over` overriding matching keys in `under`."""
merged(under::Dict, over::Dict)::Dict = merge(under, over)
merged(under::Any, over::Any)::Any = something(over, under, Some(nothing))

"""`over`'s keys where it sets them, else `under`'s; nested dictionaries are merged."""
overlay(under::Preferences, over::Preferences)::Preferences = Preferences(
    merged.(getfield.((under,), fieldnames(Preferences)), getfield.((over,), fieldnames(Preferences)))...
)

"""The preferences in the TOML `file` below the `path` of table names (`("preferences", "Corset")`); none set when there is no file or table."""
function read_preferences(file::AbstractString, path::Tuple{Vararg{String}})::Preferences # lint: unstable-variable  TOML tables are Dict{String, Any}
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
            throw(UsageError("[$(join(path, "."))] in $file: $(sprint(showerror, error_))"))
        end
        rethrow() # COV_EXCL_LINE
    end
end

"""
    load_config(root)

The `Config` of the project at `root`: the `[preferences.Corset]` table of its Project.toml overlaid by
the `[Corset]` table of its LocalPreferences.toml, key by key. An unknown key, an unknown rule name or a
level other than `allow`, `warn` or `deny`, or a set directory that does not exist, throws, so a typo cannot
silently switch a rule off or skip a directory.
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
        if rule ∉ check_names()
            throw(UsageError("[preferences.Corset.levels] names no rule $(repr(rule)); the rules are $(join(check_names(), ", "))"))
        end
        if level ∉ LEVELS
            throw(UsageError("[preferences.Corset.levels] sets $rule to $(repr(string(level))); a level is one of $(join(LEVELS, ", "))"))
        end
    end
    return Config(
        Tuple(configured_directories(root, prefs.directories)),
        prefs.baseline,
        Tuple(Symbol.(something(prefs.one_letter_exempt, String[]))),
        Tuple(something(prefs.skipped_directories, String[])),
        something(prefs.pedantic, false),
        levels,
        checked_limit(something(prefs.candidate_limit, DEFAULT_CANDIDATE_LIMIT), "[preferences.Corset] candidate_limit"),
        entry_point(prefs.entry_points),
        checked_line_limit(something(prefs.file_line_limit, DEFAULT_FILE_LINE_LIMIT), "[preferences.Corset] file_line_limit"),
        checked_field_limit(something(prefs.struct_field_limit, DEFAULT_STRUCT_FIELD_LIMIT), "[preferences.Corset] struct_field_limit"),
        something(prefs.strict_captures, false),
        Tuple(forbidden_pattern.(something(prefs.forbidden_patterns, ForbiddenPatternPreference[]))),
        Tuple(something(prefs.banned_words, String[])),
        Tuple(something(prefs.banned_suffixes, String[])),
    )
end

"""The `ForbiddenPattern` of entry `entry`; a pattern that does not compile throws a `UsageError`."""
function forbidden_pattern(entry::ForbiddenPatternPreference)::ForbiddenPattern # lint: unmarked-mutation  builds a tuple of the vector's length
    pattern = compiled_pattern(entry.pattern, "pattern of $(repr(entry.name))")
    unless = nothing
    if !isnothing(entry.unless)
        unless = compiled_pattern(entry.unless, "unless of $(repr(entry.name))")
    end
    return ForbiddenPattern(entry.name, pattern, entry.message, unless, Tuple(entry.skip_files)) # lint: runtime-dispatch  a tuple of the vector's length
end

"""The `Regex` of `text`; one that does not compile throws a `UsageError` naming `what`."""
function compiled_pattern(text::AbstractString, what::AbstractString)::Regex
    try
        return Regex(text)
    catch error_
        if error_ isa ErrorException
            throw(UsageError("[preferences.Corset.forbidden_patterns] $what does not compile: $(sprint(showerror, error_))"))
        end
        rethrow() # COV_EXCL_LINE
    end
end

"""
The `directories` setting: `src` when unset, which may be absent. A set directory missing under `root`
throws; one inside another listed one is dropped, so no file is read twice.
"""
configured_directories(::AbstractString, ::Nothing)::Vector{String} = ["src"]

function configured_directories(root::AbstractString, directories::AbstractVector{String})::Vector{String}
    absent = directories[.!isdir.(joinpath.(root, directories))]
    if !isempty(absent)
        throw(UsageError("[preferences.Corset] directories names $(join(repr.(absent), ", ")), missing under $root"))
    end
    paths = unique(directory_path.(directories))
    return paths[.!vec(any(holds.(permutedims(paths), paths); dims = 2))]
end

"""Relative directory path `directory` normalized: no `.` part and no trailing separator."""
directory_path(directory::AbstractString)::String = dirname(joinpath(normpath(directory), ""))

"""Whether directory path `outer` strictly holds directory path `inner`; both are normalized and relative."""
function holds(outer::AbstractString, inner::AbstractString)::Bool
    outer_parts, inner_parts = splitpath(outer), splitpath(inner)
    return length(inner_parts) > length(outer_parts) && inner_parts[eachindex(outer_parts)] == outer_parts
end

"""The `file => function` of an `entry_points` setting `\"file.jl:function\"`; `nothing` when unset. Any other shape throws."""
entry_point(::Nothing)::Nothing = nothing

function entry_point(setting::AbstractString)::Pair{String, Symbol}
    pieces = rsplit(setting, ':'; limit = 2)
    if length(pieces) != 2 || any(isempty, pieces)
        throw(UsageError("[preferences.Corset] entry_points is $(repr(setting)); write it as \"file.jl:function\""))
    end
    return String(first(pieces)) => Symbol(last(pieces))
end

"""`limit`, a `candidate_limit` set by `source`; a negative one throws."""
function checked_limit(limit::Integer, source::AbstractString)::Int
    if limit < 0
        throw(UsageError("$source is $limit; 0 lists no runtime-dispatch candidates, a positive count caps them"))
    end
    return limit
end

"""The `Repository` for `config` rooted at `root`; a relative baseline path is taken from `root`."""
function repository(config::Config, root::AbstractString)::Repository
    baseline = nothing
    if !isnothing(config.baseline)
        baseline = abspath(root, config.baseline)
    end
    return Repository( # lint: runtime-dispatch  the keyword call checks the tuple settings once per run
        root;
        baseline,
        one_letter_exempt = config.one_letter_exempt,
        skipped_directories = config.skipped_directories,
        config.file_line_limit,
        config.struct_field_limit,
        config.strict_captures,
        config.forbidden_patterns,
        config.banned_words,
        config.banned_suffixes,
    )
end

"""The level `config` gives `check`: its own setting, else `:warn` for the default group and for the pedantic group when on."""
function level(config::Config, check::Check)::Symbol
    if haskey(config.levels, check.name)
        return config.levels[check.name]
    end
    return ifelse(check.group === :default || config.pedantic, :warn, :allow)
end

"""The level `config` gives `rule`, which has one check; a rule with sub-checks has a level per check."""
level(config::Config, rule::Rule)::Symbol = level(config, only(checks(rule)))

# The check every code-quality rule reports through. A rule hands `ratchet!` the sites it found. With no
# baseline every site fails; a baseline file allows the sites it holds and falls when a run finds fewer.

using Test: @test
using TOML: TOML

# The baseline file holds one table per rule, named as in the rule's opt-out comment. A string
# is a named offender's note ("unassigned" waits on a decision, "kept: …" is deliberate) and
# allows it at any number of sites; an integer allows that many sites. `TOML.print` drops comments.

"""
    Repository(root; baseline = nothing, one_letter_exempt = (), skipped_directories = ())

The tree the rules read, and the settings that relax them. The defaults are the strict reading: every
finding of every rule fails. `root` is the tree whose source the rules read (made absolute).

- `baseline`: the TOML file of per-rule allowances that `ratchet!` holds findings to; `nothing` allows none.
  It may be a link: `ratchet!` resolves it at each call, so a lowering lands in the file it points to.
- `one_letter_exempt`: the variable names the one-letter rule allows besides `_` (a project's own
  convention, such as an argument everywhere named `p`).
- `skipped_directories`: directory names `repository_sources` leaves out wherever they sit, such as
  `("vendor",)`. Hidden directories (a leading `.`) are always left out.
"""
struct Repository
    root::String
    baseline::Union{String, Nothing}
    one_letter_exempt::Tuple{Vararg{Symbol}}
    skipped_directories::Tuple{Vararg{String}}
end
Repository(
    root::AbstractString;
    baseline::Union{String, Nothing} = nothing,
    one_letter_exempt::Tuple{Vararg{Symbol}} = (),
    skipped_directories::Tuple{Vararg{String}} = (),
)::Repository = Repository(abspath(root), baseline, one_letter_exempt, skipped_directories)

"""
One offender a rule found: `key` names it in the baseline; `file` (a path, empty when the offender
has none) and the lines `line` through `last_line` place it for the opt-out comments, so a comment on
any of them takes the site out. Line 0 places it in the file as a whole. `detail` tells the reader of the
log what the offender is (a variable and its type, say); a rule with nothing to add passes `""`, and
the constructors have no default so no rule forgets it.
"""
struct Site
    key::String
    file::String
    line::Int
    last_line::Int
    detail::String
end
Site(key::String, file::String, line::Integer, detail::String) = Site(key, file, line, line, detail)

"""
`# lint: RULE` opts its own line out of `RULE`, `# lint: RULE-begin` … `# lint: RULE-end` the lines
between (inclusive), `# lint: RULE-file` the whole file; the reason follows on the comment. A rule
name is lowercase words joined by `-`.
"""
const OPT_OUT = r"#\s*lint:\s*([a-z0-9]+(?:-[a-z0-9]+)*?)(?:-(file|begin|end))?(?![\w-])"

"""Which lines of one file a rule skips: all of them when `whole_file`, else `lines`."""
struct OptOuts
    whole_file::Bool
    lines::Set{Int}
end

"""
    opt_outs(path, rule)

The lines of `path` that the `# lint:` comments (`OPT_OUT`) take out of `rule`. A `-begin` without
an `-end` runs to the end of the file. A path that is no file (a method a macro defined has the file
`none`) has none.
"""
function opt_outs(path::AbstractString, rule::AbstractString)::OptOuts
    whole_file = false
    lines = Set{Int}()
    if !isfile(path)
        return OptOuts(whole_file, lines)
    end
    inside = false
    for (number, text) in enumerate(eachline(path))
        if inside
            push!(lines, number)
        end
        for found in eachmatch(OPT_OUT, text)
            if found[1] != rule
                continue
            end
            push!(lines, number)
            if found[2] == "file"
                whole_file = true
            elseif found[2] == "begin"
                inside = true
            elseif found[2] == "end"
                inside = false
            end
        end
    end
    return OptOuts(whole_file, lines)
end

"""The Julia files below `directory`, in no particular order; hidden directories, those named in `skipped` and links to directories are not entered."""
function julia_files(directory::AbstractString, skipped::Tuple{Vararg{String}})::Vector{String}
    entries = readdir(directory; join = true)
    entered = filter(Base.Fix2(entered_directory, skipped), entries)
    return reduce(vcat, julia_files.(entered, (skipped,)); init = filter(julia_file, entries))
end

"""Whether `julia_files` enters `entry`: a directory, not a link, not hidden and not named in `skipped`."""
entered_directory(entry::AbstractString, skipped::Tuple{Vararg{String}})::Bool =
    isdir(entry) && !islink(entry) && !startswith(basename(entry), ".") && !(basename(entry) in skipped)

"""Whether `entry` is a Julia file."""
julia_file(entry::AbstractString)::Bool = !isdir(entry) && endswith(entry, ".jl")

"""The Julia files under `directories` of `repository`; hidden directories and its `skipped_directories` are left out."""
repository_sources(repository::Repository, directories::Tuple{Vararg{String}})::Vector{String} = sort!(
    reduce(vcat, julia_files.(joinpath.(repository.root, directories), (repository.skipped_directories,)); init = String[]),
)

"""The baseline entry left after `found` sites against `entry`: a note stays while its offender has a site, a count falls to `found`."""
remaining(entry::AbstractString, found::Integer)::Union{String, Int} = ifelse(found == 0, 0, entry)
remaining(entry::Integer, found::Integer)::Int = min(entry, found)

"""Whether `found` sites exceed baseline `entry`; a note allows any number."""
exceeds(found::Integer, entry::AbstractString)::Bool = false
exceeds(found::Integer, entry::Integer)::Bool = found > entry

"""A baseline file: per rule, the allowance (a count or a note) of each offender."""
const Baseline = Dict{String, Dict{String, Union{Int, String}}}

"""The baseline in the TOML file at `path`."""
read_baseline(path::AbstractString)::Baseline =
    Baseline(rule => Dict{String, Union{Int, String}}(entries) for (rule, entries) in TOML.parsefile(path))

"""Write `baseline` to the file at `path` in one rename, so a reader never sees half a file."""
function write_baseline!(baseline::Baseline, path::AbstractString)::String
    buffer = IOBuffer()
    TOML.print(buffer, baseline; sorted = true)
    staged = "$path.$(getpid())"
    write(staged, take!(buffer))
    return mv(staged, path; force = true)
end

"""The `detail`s of the sites under each key, sorted and joined; a key none of whose sites has one is absent."""
function detail_lines(sites::AbstractVector{S})::Dict{String, String} where {S <: Site}
    described = [site for site in sites if !isempty(site.detail)]
    keys_ = unique([site.key for site in described])
    return Dict{String, String}(keys_ .=> key_details.((described,), keys_))
end

"""The `detail`s of the `sites` under `key`, sorted and joined."""
key_details(sites::AbstractVector{<:Site}, key::String)::String =
    join(sort!(unique([site.detail for site in sites if site.key == key])), "; ")

"""The parenthesized detail that follows `key` in the log, empty when `key` has none."""
function detail_suffix(details::AbstractDict{String, String}, key::String)::String
    if haskey(details, key)
        return " ($(details[key]))"
    end
    return ""
end

"""The log line of offender `key`: its count in `measured` and its `details`."""
over_line(measured::AbstractDict{String, Int}, details::AbstractDict{String, String}, key::String)::String =
    "$key = $(measured[key])" * detail_suffix(details, key)

"""Log `over`, the keys of `measured` past what `allowance` names allows, each with its `details`, and with `fix` (how to repair one) when given; return `over`."""
function logged_over(
        rule::String, measured::AbstractDict{String, Int}, details::AbstractDict{String, String}, over::AbstractVector{String}, allowance::String, fix::String,
    )::Vector{String}
    if !isempty(over)
        advice = ifelse(isempty(fix), "", "\nFix: $fix")
        lines = over_line.((measured,), (details,), over)
        @error "$rule: offenders past $allowance:\n" * join(lines, "\n") * advice
    end
    return over
end

"""The sites of `sites` that no `# lint:` comment naming `rule` opts out, and how many were opted out."""
function unopted(sites::AbstractVector{S}, rule::AbstractString)::Tuple{Vector{Site}, Int} where {S <: Site}
    skips = Dict{String, OptOuts}()
    kept = Site[]
    for site in sites
        if !haskey(skips, site.file)
            skips[site.file] = opt_outs(site.file, rule)
        end
        if !(skips[site.file].whole_file || any(in(skips[site.file].lines), site.line:site.last_line))
            push!(kept, site)
        end
    end
    return kept, length(sites) - length(kept)
end

"""The number of `sites` under each key."""
function tally(sites::AbstractVector{S})::Dict{String, Int} where {S <: Site}
    measured = Dict{String, Int}()
    for site in sites
        measured[site.key] = get(measured, site.key, 0) + 1
    end
    return measured
end

"""The keys of `measured` that baseline table `entries` does not allow: absent from it, or past their count."""
function exceeding(entries::AbstractDict, measured::AbstractDict{String, Int})::Vector{String}
    names = collect(String, keys(measured))
    return sort!(names[exceeded.((entries,), (measured,), names)])
end

"""Whether baseline table `entries` does not allow the `measured` count of `key`: absent, or past its count."""
exceeded(entries::AbstractDict, measured::AbstractDict{String, Int}, key::String)::Bool =
    !haskey(entries, key) || exceeds(measured[key], entries[key])

"""The keys of `entries` under one of `scopes` that `measured` undercuts, so their entry can be lowered."""
function falling(entries::AbstractDict, measured::AbstractDict{String, Int}, scopes::Tuple{Vararg{String}})::Vector{String}
    names = collect(String, keys(entries))
    return sort!(names[falls.((entries,), (measured,), (scopes,), names)])
end

"""Whether `key` of `entries` is under one of `scopes` and `measured` undercuts its entry."""
falls(entries::AbstractDict, measured::AbstractDict{String, Int}, scopes::Tuple{Vararg{String}}, key::String)::Bool =
    any(startswith.(key, scopes)) && remaining(entries[key], get(measured, key, 0)) != entries[key]

"""
    offenders!(repository, rule, sites; scopes = ("",), fix = "")

The keys of `rule`'s offenders `sites` that `repository` does not allow, logged. Sites that a `# lint:`
comment naming the rule opts out are dropped and counted in the log; the rest are tallied by key.
Without a baseline (`Repository`'s default) every key is returned. With one, the offenders are held to
`rule`'s table in the baseline file: the keys past their entry are returned, and an entry the tally
undercuts is lowered or deleted and the file rewritten. A rule with no table is seeded with its tally.
Several testsets may share one rule's table, and a run may not measure all of it (a partial copy of
the tree): each passes the prefixes `scopes` that begin the keys it measures, and only entries under
one of them can fall. `fix` tells the reader of the log how to repair an offender, such as the forms
the rule accepts.
"""
function offenders!(
        repository::Repository, rule::String, sites::AbstractVector{Site}; scopes::Tuple{Vararg{String}} = ("",), fix::String = "",
    )::Vector{String}
    kept, opted = unopted(sites, rule)
    measured = tally(kept)
    if opted > 0
        @info "$rule: $opted site(s) opted out by `# lint: $rule`"
    end
    baseline_file = repository.baseline
    if isnothing(baseline_file)
        return logged_over(rule, measured, detail_lines(kept), sort!(collect(keys(measured))), "no baseline", fix)
    end
    # ponytail: testsets on separate processes may rewrite at once; the rename is atomic, so
    # one lowering can be lost (the baseline stays higher, never wrong) and the next run redoes it.
    path = realpath(baseline_file)
    baseline = read_baseline(path)
    if !haskey(baseline, rule)
        baseline[rule] = Dict{String, Union{Int, String}}(measured)
        write_baseline!(baseline, path)
        @warn "$rule: no table in $path; seeded with today's $(sum(values(measured); init = 0)) site(s)"
        return String[]
    end
    entries = baseline[rule]
    over = exceeding(entries, measured)
    improved = falling(entries, measured, scopes)
    for key in improved
        left = remaining(entries[key], get(measured, key, 0))
        if left == 0
            delete!(entries, key)
        else
            entries[key] = left
        end
    end
    if !isempty(improved)
        write_baseline!(baseline, path)
        @info "$rule fell: baseline lowered in $path" improved
    end
    return logged_over(rule, measured, detail_lines(kept), over, "the baseline in $path", fix)
end

"""
    ratchet!(repository, rule, sites; scopes = ("",), fix = "")

A test that `rule`'s offenders `sites` are all allowed: it fails on the keys `offenders!` returns, and
returns them.
"""
function ratchet!(
        repository::Repository, rule::String, sites::AbstractVector{Site}; scopes::Tuple{Vararg{String}} = ("",), fix::String = "",
    )::Vector{String}
    over = offenders!(repository, rule, sites; scopes, fix)
    @test isempty(over)
    return over
end

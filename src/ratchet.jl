# The check every code-quality rule reports through. A rule hands `ratchet!` the sites it found. With no
# baseline every site fails; a baseline file allows the sites it holds and falls when a run finds fewer.

using Test: @test
using TOML: TOML

const SYNTAX = Base.JuliaSyntax # lint: non-public-access  the registered JuliaSyntax lags the parser Julia 1.13 ships

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

"""One `# lint:` comment: the `rule` it names, its `form` (`:line`, `:file`, `:begin` or `:end`) and its `line`."""
struct OptOutComment
    rule::String
    form::Symbol
    line::Int
end

const COMMENT_KIND = SYNTAX.@K_str "Comment"

"""
    opt_out_comments(path, text = read(path, String))

The `# lint:` comments (`OPT_OUT`) of the Julia source `text` of file `path`: matches inside comment
tokens only, so a string or docstring that quotes one opts nothing out. A `-begin` with no `-end` of
its rule below it throws. A path that is no file (a method a macro defined has the file `none`) has none.
"""
function opt_out_comments(path::AbstractString)::Vector{OptOutComment}
    if !isfile(path)
        return OptOutComment[]
    end
    return opt_out_comments(path, read(path, String))
end

function opt_out_comments(path::AbstractString, text::AbstractString)::Vector{OptOutComment}
    source = SYNTAX.SourceFile(text)
    tokens = [token.range for token in SYNTAX.tokenize(text) if SYNTAX.kind(token) == COMMENT_KIND]
    comments = [
        OptOutComment(found[1], opt_out_form(found[2]), SYNTAX.source_line(source, Int(first(range)) + found.offset - 1))
            for range in tokens for found in eachmatch(OPT_OUT, SubString(text, first(range), thisind(text, last(range))))
    ]
    unclosed = comments[open_begin.((comments,), comments)]
    if !isempty(unclosed)
        error("$path:$(first(unclosed).line): `# lint: $(first(unclosed).rule)-begin` has no `# lint: $(first(unclosed).rule)-end` below it")
    end
    return comments
end

"""The form an `OPT_OUT` suffix (`file`, `begin`, `end` or none) gives its comment."""
opt_out_form(suffix::AbstractString)::Symbol = Symbol(suffix)
opt_out_form(::Nothing)::Symbol = :line

"""Whether `comment` is a `-begin` that no `-end` of its rule among `comments` closes, on its line or below."""
open_begin(comments::AbstractVector{OptOutComment}, comment::OptOutComment)::Bool =
    comment.form === :begin && isempty(closing_lines(comments, comment))

"""The lines of the `-end`s among `comments` that can close `opening`, a `-begin`: same rule, on its line or below. The first closes it."""
closing_lines(comments::AbstractVector{OptOutComment}, opening::OptOutComment)::Vector{Int} =
    [comment.line for comment in comments if comment.form === :end && comment.rule == opening.rule && comment.line >= opening.line]

"""Which lines of one file a rule skips: all of them when `whole_file`, else `lines`."""
struct OptOuts
    whole_file::Bool
    lines::Set{Int}
end

"""
    opt_outs(path, rule)
    opt_outs(comments, rule)

The lines that the `# lint:` comments of `path` (`opt_out_comments`), or `comments`, take out of `rule`:
each comment's own line, and every line from a `-begin` to the `-end` that closes it.
"""
opt_outs(path::AbstractString, rule::AbstractString)::OptOuts = opt_outs(opt_out_comments(path), rule)

function opt_outs(comments::AbstractVector{OptOutComment}, rule::AbstractString)::OptOuts
    named = [comment for comment in comments if comment.rule == rule]
    spans = [comment.line:minimum(closing_lines(named, comment)) for comment in named if comment.form === :begin]
    lines = Set{Int}(Iterators.flatten((Int[comment.line for comment in named], spans...)))
    return OptOuts(any(comment.form === :file for comment in named), lines)
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

"""The baseline entry left after `found` sites against `entry`: a note stays, a count falls to `found`."""
remaining(entry::AbstractString, ::Integer)::String = entry
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

"""
    grouped_details(groups, details)

The distinct `details` in each of `groups`, sorted and joined with `"; "`; the two vectors pair up
element by element. One sort, and a binary search per group.
"""
function grouped_details(groups::AbstractVector{G}, details::AbstractVector{String})::Dict{G, String} where {G}
    entries = sort!(unique(zip(groups, details)))
    owners = first.(entries)
    return Dict{G, String}(group => join(last.(entries[searchsorted(owners, group)]), "; ") for group in unique(groups))
end

"""The `detail`s of the sites under each key, sorted and joined; a key none of whose sites has one is absent."""
function detail_lines(sites::AbstractVector{S})::Dict{String, String} where {S <: Site}
    described = [site for site in sites if !isempty(site.detail)]
    return grouped_details(String[site.key for site in described], String[site.detail for site in described])
end

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

"""The `# lint:` comments of `file`: those `comments` holds, or else the file's own (`opt_out_comments`)."""
function file_comments(comments::AbstractDict{String, Vector{OptOutComment}}, file::String)::Vector{OptOutComment}
    if haskey(comments, file)
        return comments[file]
    end
    return opt_out_comments(file)
end

"""
The sites of `sites` that no `# lint:` comment naming `rule` opts out, and how many were opted out.
`comments` holds the comments of files already parsed, by path; any other file is read.
"""
function unopted(
        sites::AbstractVector{S}, rule::AbstractString, comments::AbstractDict{String, Vector{OptOutComment}} = Dict{String, Vector{OptOutComment}}(),
    )::Tuple{Vector{Site}, Int} where {S <: Site}
    files = unique(String[site.file for site in sites])
    skips = Dict{String, OptOuts}(files .=> opt_outs.(file_comments.((comments,), files), rule))
    kept = sites[.!opted.(getindex.((skips,), String[site.file for site in sites]), sites)]
    return kept, length(sites) - length(kept)
end

"""Whether `skips` (one file's `OptOuts`) covers a line of `site`."""
opted(skips::OptOuts, site::Site)::Bool = skips.whole_file || any(in(skips.lines), site.line:site.last_line)

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

"""The keys of `entries` under one of `scopes` that hold a note and that `measured` finds no site of."""
function stale_notes(entries::AbstractDict, measured::AbstractDict{String, Int}, scopes::Tuple{Vararg{String}})::Vector{String}
    names = collect(String, keys(entries))
    return sort!(names[stale.((entries,), (measured,), (scopes,), names)])
end

"""Whether `key` of `entries` is under one of `scopes`, holds a note, and `measured` finds no site of it."""
stale(entries::AbstractDict, measured::AbstractDict{String, Int}, scopes::Tuple{Vararg{String}}, key::String)::Bool =
    any(startswith.(key, scopes)) && entries[key] isa AbstractString && !haskey(measured, key)

"""
    offenders!(repository, rule, sites; scopes = ("",), fix = "", comments = Dict())

The keys of `rule`'s offenders `sites` that `repository` does not allow, logged. Sites that a `# lint:`
comment naming the rule opts out are dropped and counted in the log; the rest are tallied by key.
Without a baseline (`Repository`'s default) every key is returned. With one, the offenders are held to
`rule`'s table in the baseline file: the keys past their entry are returned, and a count the tally
undercuts is lowered or deleted and the file rewritten. A note stays; one with no site is logged stale.
A rule with no table is seeded with its tally.
Several testsets may share one rule's table, and a run may not measure all of it (a partial copy of
the tree): each passes the prefixes `scopes` that begin the keys it measures, and only entries under
one of them can fall. `fix` tells the reader of the log how to repair an offender, such as the forms
the rule accepts. `comments` holds the `# lint:` comments of files already parsed, by path.
"""
function offenders!(
        repository::Repository, rule::String, sites::AbstractVector{Site}; scopes::Tuple{Vararg{String}} = ("",), fix::String = "",
        comments::AbstractDict{String, Vector{OptOutComment}} = Dict{String, Vector{OptOutComment}}(),
    )::Vector{String}
    kept, opted = unopted(sites, rule, comments)
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
    stale_keys = stale_notes(entries, measured, scopes)
    if !isempty(stale_keys)
        @warn "$rule: notes with no site left, kept in $path; delete one whose offender is gone:\n" * join(stale_keys, "\n")
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

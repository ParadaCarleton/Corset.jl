# Rules that run an external tool over the repository: Fatou's linter and jscpd's duplicate finder.

# One line of `fatou lint --output concise`: file, line, column, severity, rule and message.
const FATOU_FINDING = r"^(.+?):(\d+):\d+: \w+\[([a-z0-9-]+)\] "
# Fatou's closing line, `checked N file(s): clean` or with a finding count; it is no finding.
const FATOU_SUMMARY = r"^checked \d+ file\(s\)"

"""The `directories` that exist in `repository` (a job's copy holds only `src`, `ext`, `test` and links)."""
present_directories(repository::Repository, directories::Tuple{Vararg{String}})::Tuple{Vararg{String}} =
    filter(isdir ∘ Base.Fix1(joinpath, repository.root), directories)

"""
One site per finding of `fatou lint` over `directories` of `repository`, keyed by file and Fatou
rule and placed at the finding's line (the `fatou` rule's opt-out comment takes it out). Fatou must be
installed; a run that prints a line it did not mean as a finding (a parse error) throws.
"""
function fatou_sites(repository::Repository, directories::Tuple{Vararg{String}})::Vector{
        Site,
    }
    fatou = Sys.which("fatou")
    if isnothing(fatou)
        error("fatou is not on PATH; the fatou rule runs `fatou lint`")
    end
    command = Cmd(
        `$fatou lint --color never --output concise $(collect(directories))`;
        dir = repository.root,
    )
    printed = IOBuffer()
    run(pipeline(ignorestatus(command); stdout = printed, stderr = printed))
    lines = split(String(take!(printed)), '\n'; keepempty = false)
    findings = match.(FATOU_FINDING, lines)
    unread = lines[isnothing.(findings) .& .!occursin.(FATOU_SUMMARY, lines)]
    if !isempty(unread)
        error("fatou lint printed lines that are no finding:\n" * join(unread, "\n"))
    end
    return fatou_site.(repository.root, filter(!isnothing, findings))
end

"""The site of `found`, a `FATOU_FINDING` match, in the repository at `root`."""
fatou_site(root::AbstractString, found::RegexMatch)::Site = Site("$(found[1]) $(found[3])", joinpath(root, found[1]), parse(Int, found[2]), "")

"""One `Site` from `duplicate`, an item of a `jscpd --absolute` JSON report on `repository`."""
function jscpd_site(repository::Repository, duplicate::AbstractDict)::Site
    first_file = string(duplicate["firstFile"]["name"])
    second_file = string(duplicate["secondFile"]["name"])
    rel_first = relpath(first_file, repository.root)
    rel_second = relpath(second_file, repository.root)
    start_line = Int(duplicate["secondFile"]["start"])
    end_line = Int(duplicate["secondFile"]["end"])
    return Site("$rel_second $rel_first", second_file, start_line, end_line, "")
end

"""The `Cmd` running `jscpd` against `dirs` with report written to `report_dir`."""
function jscpd_command(
        jscpd::AbstractString,
        repository::Repository,
        dirs::AbstractVector{String},
        report_dir::AbstractString,
    )::Cmd
    ignore = String[]
    if !isempty(repository.skipped_directories)
        ignore = String["--ignore", join(["**/$d/**" for d in repository.skipped_directories], ",")]
    end
    return Cmd(
        `$jscpd --mode mild --min-lines 5 --min-tokens 50 --silent --no-tips --absolute --reporters json --output $report_dir $ignore $dirs`;
        dir = repository.root,
    )
end

"""
One site per duplicate code block found by `jscpd` over `directories` of `repository`, keyed by
the duplicate file and the duplicated file, placed at the duplicate block's lines. `jscpd` must be
installed and on PATH; an execution failure throws.
"""
function jscpd_sites( # lint: abstract-local  JSON report tables are untyped
        repository::Repository,
        directories::Tuple{Vararg{String}},
    )::Vector{Site}
    jscpd = Sys.which("jscpd")
    if isnothing(jscpd)
        error("jscpd is not on PATH; the jscpd rule runs `jscpd`")
    end
    dirs = present_directories(repository, directories)
    if isempty(dirs)
        return Site[]
    end
    report_dir = mktempdir()
    try
        command = jscpd_command(jscpd, repository, collect(dirs), report_dir)
        printed = IOBuffer()
        run(pipeline(ignorestatus(command); stdout = printed, stderr = printed))
        report_file = joinpath(report_dir, "jscpd-report.json")
        if !isfile(report_file)
            unread = String(take!(printed))
            error("jscpd produced no report:\n$unread")
        end
        json = Base.require(@__MODULE__, :JSON)
        report = Base.invokelatest(json.parsefile, report_file; dicttype = Dict{String, Any})
        duplicates = report["duplicates"]
        return jscpd_site.((repository,), duplicates)
    finally
        rm(report_dir; recursive = true, force = true)
    end
end

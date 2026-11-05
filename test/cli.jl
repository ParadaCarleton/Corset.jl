# The `corset` command: configuration, rule levels, output and exit codes.

using Corset:
    Corset,
    Finding,
    RULES,
    exit_code,
    level,
    load_config,
    print_findings,
    print_rules,
    project_root,
    rule_group,
    rule_name,
    run_rules,
    with_overrides

"""A package tree under a fresh directory with the `Project.toml` text `project`, and the files `files`."""
function package_tree(project::AbstractString, files::AbstractVector{<:Pair})::String
    return write_tree(mktempdir(), ["Project.toml" => project; files])
end

"""The standard output and the exit code of `main(args)`."""
function captured_main(args::AbstractVector{String})::Tuple{String, Int}
    code = Ref(0)
    output = mktemp() do path, io
        redirect_stdout(io) do
            code[] = Corset.main(args)
        end
        close(io)
        read(path, String)
    end
    return output, code[]
end

const SOURCE_TREE = ["src/Demo.jl" => "module Demo\nf(x::T)::T where {T} = x\nend\n"]

@testset "check_project: a package loaded in this process, signatures from the caller" begin
    demo = Module(:Demo)
    Core.eval(demo, :(f(x::Int)::Int = x))
    project = "name = \"Demo\"\n[[preferences.Corset.forbidden_patterns]]\nname = \"todo\"\npattern = \"TODO\"\nmessage = \"finish it\"\n[preferences.Corset.levels]\nforbidden-pattern = \"deny\"\n"
    signatures = Type[Tuple{typeof(demo.f), Int}]
    clean = package_tree(project, SOURCE_TREE)
    @test Corset.check_project(clean, demo, signatures; out = devnull) == 0
    dirty = package_tree(project, [SOURCE_TREE; "src/Todo.jl" => "# TODO\n"])
    report = IOBuffer()
    @test Corset.check_project(dirty, demo, signatures; out = report) == 1
    @test occursin("forbidden-pattern", String(take!(report)))
end

@testset "corset: configuration" begin
    root = package_tree("name = \"Demo\"\n", SOURCE_TREE)
    config = load_config(root)
    @test config.directories == ("src",)
    @test isnothing(config.baseline)
    @test !config.pedantic
    @test level(config, only(r for r in RULES if rule_name(r) == "where-return")) === :warn
    @test level(config, only(r for r in RULES if rule_name(r) == "float64")) === :allow

    @testset "Project.toml preferences, overlaid by LocalPreferences.toml key by key" begin
        root = package_tree(
            "name = \"Demo\"\n[preferences.Corset]\npedantic = true\nbaseline = \"base.toml\"\n[preferences.Corset.levels]\nfloat64 = \"deny\"\nwhere-return = \"allow\"\n",
            [
                "LocalPreferences.toml" =>
                    "[Corset]\npedantic = false\nskipped_directories = [\"vendor\"]\n[Corset.levels]\nwhere-return = \"deny\"\n",
            ],
        )
        config = load_config(root)
        @test !config.pedantic
        @test config.baseline == "base.toml"
        @test config.skipped_directories == ("vendor",)
        @test config.levels == Dict("float64" => :deny, "where-return" => :deny)
    end

    @testset "candidate_limit: the config's, else the default; the CLI flag wins; a negative one fails loud" begin
        @test config.candidate_limit == Corset.DEFAULT_CANDIDATE_LIMIT
        limited = load_config(package_tree("name = \"D\"\n[preferences.Corset]\ncandidate_limit = 9\n", Pair[]))
        @test limited.candidate_limit == 9
        @test with_overrides(limited, false, Pair{String, Symbol}[], nothing).candidate_limit == 9
        @test with_overrides(limited, false, Pair{String, Symbol}[], 0).candidate_limit == 0
        @test_throws Corset.UsageError with_overrides(limited, false, Pair{String, Symbol}[], -1)
        @test_throws Corset.UsageError load_config(package_tree("name = \"D\"\n[preferences.Corset]\ncandidate_limit = -2\n", Pair[]))
        @test Corset.command_options(Corset.parse_args(["check", "--candidate-limit", "7"], Corset.argument_settings())).candidate_limit == 7
    end

    @testset "struct_field_limit, strict_captures, forbidden_patterns reach the Repository; a bad value fails loud" begin
        @test config.struct_field_limit == Corset.DEFAULT_STRUCT_FIELD_LIMIT
        @test !config.strict_captures
        @test isempty(config.forbidden_patterns)
        text = "name = \"D\"\n[preferences.Corset]\nstruct_field_limit = 5\nstrict_captures = true\n" *
            "[[preferences.Corset.forbidden_patterns]]\nname = \"count\"\npattern = \"n = \\\\d\"\nmessage = \"name it\"\nunless = \"ok\"\nskip_files = [\"a.jl\"]\n"
        tree = package_tree(text, Pair[])
        repository = Corset.repository(load_config(tree), tree)
        @test repository.struct_field_limit == 5
        @test repository.strict_captures
        forbidden = only(repository.forbidden_patterns)
        @test forbidden.name == "count" && forbidden.message == "name it" && forbidden.skip_files == ("a.jl",)
        @test occursin(forbidden.pattern, "n = 4") && occursin(forbidden.unless, "ok")
        @test_throws Corset.UsageError load_config(package_tree("name = \"D\"\n[preferences.Corset]\nstruct_field_limit = 0\n", Pair[]))
        broken = "name = \"D\"\n[[preferences.Corset.forbidden_patterns]]\nname = \"x\"\npattern = \"(\"\nmessage = \"m\"\n"
        @test_throws r"pattern of \"x\" does not compile" load_config(package_tree(broken, Pair[]))
    end

    @testset "file_line_limit: the config's, else the default, reaching the Repository; one below 1 fails loud" begin
        @test config.file_line_limit == Corset.DEFAULT_FILE_LINE_LIMIT
        tree = package_tree("name = \"D\"\n[preferences.Corset]\nfile_line_limit = 40\n", Pair[])
        limited = load_config(tree)
        @test limited.file_line_limit == 40
        @test Corset.repository(limited, tree).file_line_limit == 40
        @test_throws Corset.UsageError load_config(package_tree("name = \"D\"\n[preferences.Corset]\nfile_line_limit = 0\n", Pair[]))
    end

    @testset "a typo fails loud" begin
        @test_throws Corset.UsageError load_config(
            package_tree(
                "name = \"D\"\n[preferences.Corset]\npedantc = true\n",
                Pair[],
            )
        )
        @test_throws Corset.UsageError load_config(
            package_tree(
                "name = \"D\"\n[preferences.Corset.levels]\nno-such-rule = \"deny\"\n",
                Pair[],
            )
        )
        @test_throws Corset.UsageError load_config(
            package_tree(
                "name = \"D\"\n[preferences.Corset.levels]\nfloat64 = \"loud\"\n",
                Pair[],
            )
        )
        @test_throws Corset.UsageError with_overrides(config, false, ["no-such-rule" => :deny], nothing)
    end

    @testset "a configured directory that does not exist fails loud; a missing default src does not" begin
        misspelled = package_tree("name = \"D\"\n[preferences.Corset]\ndirectories = [\"scr\"]\n", SOURCE_TREE)
        @test_throws Corset.UsageError load_config(misspelled)
        redirect_stderr(devnull) do
            @test captured_main(["check", misspelled, "--no-load"])[2] == 2
        end
        @test load_config(package_tree("name = \"D\"\n", Pair[])).directories == ("src",)
        nested = package_tree("name = \"D\"\n[preferences.Corset]\ndirectories = [\"src\", \"ext/Foo\"]\n", [SOURCE_TREE; "ext/Foo/Foo.jl" => "module Foo\nend\n"])
        @test load_config(nested).directories == ("src", "ext/Foo")
    end

    @test_throws Corset.UsageError project_root(mktempdir())
end

@testset "corset: entry signatures for the typed rules" begin
    @test Corset.entry_sources(nothing) == [:compiled, :declared]
    @test Corset.entry_sources("workload,tests,workload") == [:compiled, :declared, :tests]
    @test isempty(Corset.entry_sources("none"))
    @test_throws Corset.UsageError Corset.entry_sources("nowhere")
    @test_throws Corset.UsageError Corset.entry_sources("none,tests")
    @test Corset.command_options(Corset.parse_args(["check", "--entries", "tests"], Corset.argument_settings())).entries == "tests"

    @test Corset.entry_point("test/entries.jl:signatures") == ("test/entries.jl" => :signatures)
    @test_throws Corset.UsageError Corset.entry_point("entries.jl")
    @test_throws Corset.UsageError Corset.entry_point("entries.jl:")

    mod = Corset.WorkloadPackage
    mod.bump(1)
    plain = package_tree("name = \"WorkloadPackage\"\n", Pair[])
    sources = Corset.seed_sources(load_config(plain), plain, nothing, mod, devnull)
    @test first.(sources) == ["compiled", "declared"]
    @test Tuple{typeof(mod.bump), Int} in last(first(sources))
    frames = Corset.seeded_frames(sources, mod)
    @test Tuple{typeof(mod.bump), Int} in [frame.code.parent.specTypes for frame in frames]
    compiled = length(last(first(sources)))
    @test Corset.seed_summary(sources, frames, 3 * 2^20 + 1) ==
        "entry signatures: compiled $compiled, declared 0; $compiled seeds, $(length(frames)) frames kept; peak RSS 3 MiB"
    @test sprint(Corset.warn_tests!, [:compiled, :tests]) ==
        "warning: --entries tests runs the package's whole test suite, and every process it starts, beside this one\n"
    @test isempty(sprint(Corset.warn_tests!, [:compiled, :declared]))

    configured = package_tree(
        "name = \"WorkloadPackage\"\n[preferences.Corset]\nentry_points = \"entries.jl:signatures\"\n",
        ["entries.jl" => "signatures() = Type[Tuple{typeof(identity), Symbol}]\n"],
    )
    config = load_config(configured)
    @test config.entry_points == ("entries.jl" => :signatures)
    @test Corset.seed_sources(config, configured, nothing, mod, devnull) == ["entry_points" => Type[Tuple{typeof(identity), Symbol}]]
    @test_throws Corset.UsageError Corset.seed_sources(config, configured, "workload", mod, devnull)
end

@testset "corset: every rule has a unique name and a known group" begin
    names = rule_name.(RULES)
    @test allunique(names)
    @test all(group in (:default, :pedantic) for group in rule_group.(RULES))
    @test sort!([rule_name(rule) for rule in RULES if rule_group(rule) === :pedantic]) == [
        "c-type", "concrete-return", "file-length", "float64", "jscpd", "nothing-return", "one-letter",
        "quadratic-scan", "range-guard", "ref", "repeated-prefix", "struct-constant", "wide-struct",
    ]
end

@testset "corset: running the rules" begin
    root = package_tree("name = \"Demo\"\n", SOURCE_TREE)
    findings, skipped = run_rules(load_config(root), root)
    @test [(finding.rule, finding.site.line) for finding in findings] ==
        [("where-return", 2)]
    @test "hidden-input" in skipped

    @testset "a # lint: comment opts a site out" begin
        opted = package_tree(
            "name = \"Demo\"\n",
            [
                "src/Demo.jl" =>
                    "module Demo\nf(x::T)::T where {T} = x # lint: where-return\nend\n",
            ],
        )
        @test isempty(first(run_rules(load_config(opted), opted)))
    end

    @testset "a baseline allows today's sites and is read, not written" begin
        baselined = package_tree(
            "name = \"Demo\"\n[preferences.Corset]\nbaseline = \"base.toml\"\n",
            [SOURCE_TREE; "base.toml" => "[where-return]\n\"src/Demo.jl\" = 1\n"],
        )
        before = read(joinpath(baselined, "base.toml"), String)
        @test isempty(first(run_rules(load_config(baselined), baselined)))
        @test read(joinpath(baselined, "base.toml"), String) == before
    end

    @testset "--update-baseline seeds a missing baseline" begin
        seeded = package_tree(
            "name = \"Demo\"\n[preferences.Corset]\nbaseline = \"base.toml\"\n",
            SOURCE_TREE,
        )
        @test_logs (:warn, r"seeded") match_mode = :any run_rules(
            load_config(seeded),
            seeded;
            update_baseline = true,
        )
        @test occursin("where-return", read(joinpath(seeded, "base.toml"), String))

        nested = package_tree(
            "name = \"Demo\"\n[preferences.Corset]\nbaseline = \"sub/base.toml\"\n",
            SOURCE_TREE,
        )
        run_rules(load_config(nested), nested; update_baseline = true)
        @test isfile(joinpath(nested, "sub", "base.toml"))
    end

    @testset "--fix rewrites the file for the rules that have a fixer" begin
        fixed = package_tree("name = \"Demo\"\n", SOURCE_TREE)
        @test isempty(first(run_rules(load_config(fixed), fixed; fix = true)))
        @test occursin(
            "(f(x::T)::T) where {T}",
            read(joinpath(fixed, "src", "Demo.jl"), String),
        )
    end

    @testset "--diff shows the --fix rewrite and writes nothing" begin
        previewed = package_tree("name = \"Demo\"\n", SOURCE_TREE)
        before = read(joinpath(previewed, "src", "Demo.jl"), String)
        output, code = captured_main(["check", previewed, "--diff"])
        @test code == 1
        @test occursin("--- a/src/Demo.jl", output)
        @test occursin("+(f(x::T)::T) where {T}", output)
        @test read(joinpath(previewed, "src", "Demo.jl"), String) == before

        clean = package_tree(
            "name = \"Demo\"\n",
            ["src/Demo.jl" => "module Demo\ng(x) = x\nend\n"],
        )
        @test captured_main(["check", clean, "--diff"]) == ("", 0)
        @test captured_main(["check", previewed, "--diff", "--fix"])[2] == 2
    end

    @testset "--diff copies a nested directory, and a directory inside another once" begin
        extension = package_tree(
            "name = \"Demo\"\n[preferences.Corset]\ndirectories = [\"ext/Foo\"]\n",
            ["ext/Foo/Foo.jl" => "module Foo\nf(x::T)::T where {T} = x\nend\n"],
        )
        output, code = captured_main(["check", extension, "--diff"])
        @test code == 1 && occursin("--- a/ext/Foo/Foo.jl", output)
        overlapping = package_tree(
            "name = \"Demo\"\n[preferences.Corset]\ndirectories = [\"src\", \"src/sub/\", \"./src\"]\n",
            ["src/sub/inner.jl" => "f(x::T)::T where {T} = x\n"],
        )
        @test load_config(overlapping).directories == ("src",)
        output, code = captured_main(["check", overlapping, "--diff"])
        @test code == 1 && count("--- a/src/sub/inner.jl", output) == 1
        @test length(first(run_rules(load_config(overlapping), overlapping))) == 1
    end

    @testset "where-return handles unbraced where T and unbound arguments" begin
        unbraced = package_tree(
            "name = \"Demo\"\n",
            [
                "src/Demo.jl" => "module Demo\nf(x::T)::T where T = x\ng(x::Integer)::T where {T} = convert(T, x)\nend\n",
            ],
        )
        @test length(run_rules(load_config(unbraced), unbraced)[1]) == 2
        findings, _ = run_rules(load_config(unbraced), unbraced; fix = true)
        @test length(findings) == 1
        @test only(findings).rule == "where-return"
        @test occursin("(f(x::T)::T) where T = x", read(joinpath(unbraced, "src", "Demo.jl"), String))
        @test occursin("g(x::Integer)::T where {T} = convert(T, x)", read(joinpath(unbraced, "src", "Demo.jl"), String))
    end

    @testset "module rules run on a loaded package" begin
        root = package_tree("name = \"Counted\"\n", ["src/Counted.jl" => "module Counted\ncounter = 0\nbump(x::Int) = x + counter\nend\n"])
        holder = Module(:Holder)
        Base.include(holder, joinpath(root, "src", "Counted.jl"))
        config = with_overrides(load_config(root), false, ["hidden-input" => :deny], nothing)
        findings, skipped = run_rules(config, root; mod = holder.Counted, frames = entry_frames(concrete_signatures(holder.Counted), holder.Counted))
        @test ("hidden-input", :deny) in
            [(finding.rule, finding.level) for finding in findings]
        @test isempty(skipped)
    end
end

@testset "corset: output and exit codes" begin
    root = package_tree("name = \"Demo\"\n", SOURCE_TREE)
    findings, _ = run_rules(load_config(root), root)
    human = sprint(print_findings, root, findings, "human")
    @test human == "warn[where-return]: src/Demo.jl\n  --> src/Demo.jl:2\n"
    @test sprint(print_findings, root, findings, "concise") ==
        "src/Demo.jl:2: warn: [where-return] src/Demo.jl\n"
    @test occursin(
        "\"rule\":\"where-return\"",
        sprint(print_findings, root, findings, "json"),
    )
    @test sprint(
        print_findings,
        root,
        [Finding("jet", :deny, Corset.Site("scope", "", 0, ""))],
        "human",
    ) ==
        "deny[jet]: scope\n"
    described = [Finding("impure-anonymous-function", :deny, Corset.Site("a.jl f", joinpath(root, "a.jl"), 3, "holds a Core.Box"))]
    @test sprint(print_findings, root, described, "human") == "deny[impure-anonymous-function]: a.jl f\n  --> a.jl:3\n  = holds a Core.Box\n"
    @test sprint(print_findings, root, described, "concise") == "a.jl:3: deny: [impure-anonymous-function] a.jl f (holds a Core.Box)\n"
    @test occursin("\"detail\":\"holds a Core.Box\"", sprint(print_findings, root, described, "json"))

    @test exit_code(findings, false) == 0
    @test exit_code(findings, true) == 1
    @test exit_code([Finding("x", :deny, Corset.Site("k", "", 0, ""))], false) == 1
    @test exit_code(Finding[], true) == 0

    @test occursin("where-return", sprint(print_rules, load_config(root)))
    @test occursin(r"\nbroad-catch +default +warn ", sprint(print_rules, load_config(root)))
end

@testset "corset: the command" begin
    root = package_tree("name = \"Demo\"\n", SOURCE_TREE)
    output, code = captured_main(["check", root, "--no-load", "--format", "concise"])
    @test (output, code) == ("src/Demo.jl:2: warn: [where-return] src/Demo.jl\n", 0)
    @test captured_main(["check", root, "--no-load", "--deny-warnings"])[2] == 1
    @test captured_main(["check", root, "--no-load", "--deny", "where-return"])[2] == 1
    @test captured_main(["check", root, "--no-load", "--allow", "where-return"]) == ("", 0)
    @test occursin("float64", first(captured_main(["rules", root, "--pedantic"])))
    @test captured_main(["check", root, "--no-load", "--allow", "no-such-rule"])[2] == 2
    redirect_stderr(devnull) do
        @test captured_main(["check", root, "--no-load", "--entries", "bogus"])[2] == 2
        @test captured_main(["check", root, "--no-load", "--entries", "tests"])[2] == 2
        for flags in (["--format", "json"], ["--format", "human"], ["--deny-warnings"], ["--update-baseline"], ["--entries", "workload"], ["--candidate-limit", "3"])
            @test captured_main(["check", root, "--diff", flags...]) == ("", 2)
        end
    end
    configured = package_tree("name = \"Demo\"\n[preferences.Corset]\nentry_points = \"entries.jl:signatures\"\n", SOURCE_TREE)
    @test_throws Corset.UsageError Corset.checked_options(Corset.command_options(Corset.parse_args(["check", "--entries", "workload"], Corset.argument_settings())), load_config(configured))
    @test_throws Corset.UsageError Corset.load_package(
        package_tree(
            "version = \"1\"\n",
            Pair[],
        )
    )
end

@testset "corset: a rule that reads the package runs it in the project's environment" begin
    project = package_tree(
        "name = \"Demo\"\nuuid = \"aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee\"\n",
        [
            "src/Demo.jl" =>
                "module Demo\nconst COUNTER = Ref(0)\nbump(x) = x + COUNTER[]\nend\n",
        ],
    )
    command = `$(Base.julia_cmd()) --startup-file=no --project=$(dirname(@__DIR__)) -e "using Corset; exit(Corset.main(ARGS))" -- check $project --format concise --deny hidden-input`
    process = run(pipeline(ignorestatus(command); stdout = joinpath(project, "out.txt")))
    @test process.exitcode == 1
    @test occursin("hidden-input] COUNTER", read(joinpath(project, "out.txt"), String))
end

@testset "corset: every pedantic rule reports on a source that breaks it" begin
    root = mktempdir()
    fixture = load_fixture(joinpath(root, "src"))
    smells = join((SNIPPETS[name]["source"] for name in ("nothing-return", "range-guard", "return-type", "concrete-arg", "concrete-return", "float64", "c-type", "ref", "annotation", "one-letter", "fatou", "jscpd", "quadratic-scan")), "\n")
    write(joinpath(root, "src", "smells.jl"), smells)
    write(joinpath(root, "Project.toml"), "name = \"Demo\"\n[preferences.Corset]\nstruct_field_limit = 1\nfile_line_limit = 1\n")
    config = with_overrides(load_config(root), true, Pair{String, Symbol}[], nothing)
    findings, skipped = run_rules(config, root; mod = fixture, frames = entry_frames(concrete_signatures(fixture), fixture))
    @test isempty(skipped)
    pedantic = [rule_name(rule) for rule in RULES if rule_group(rule) === :pedantic]
    @test setdiff(pedantic, Set(finding.rule for finding in findings)) == String[]
    @test "jet" in Set(finding.rule for finding in findings)
end

@testset "corset: JET sites need the caller's JET" begin
    @test_throws Corset.UsageError Corset.loaded_jet(Dict{Base.PkgId, Module}())
    @test Corset.loaded_jet() isa Module
end

"""An output stream whose every write throws `failure`."""
struct FailingStream{E <: Exception} <: IO
    failure::E
end
Base.write(stream::FailingStream, ::String)::Nothing = throw(stream.failure)

@testset "corset: a write failure ends the run" begin
    root = package_tree("name = \"Demo\"\n", SOURCE_TREE)
    @test Corset.run_command(["rules", root], FailingStream(Base.IOError("write", Base.UV_EPIPE)), devnull) == 0
    report = IOBuffer()
    @test Corset.run_command(["rules", root], FailingStream(DomainError(1)), report) == 3
    @test startswith(String(take!(report)), "corset: internal error: DomainError")
    @test Corset.run_command(["rules", root], FailingStream(ErrorException("bug")), report) == 3
    @test startswith(String(take!(report)), "corset: internal error: bug")
    @test Corset.run_command(["rules", root], FailingStream(Corset.UsageError("misuse")), report) == 2
    @test String(take!(report)) == "corset: misuse\n"
    @test Corset.run_command(["rules", root], FailingStream(Corset.Entries.SourceError("no tests")), report) == 2
    @test String(take!(report)) == "corset: no tests\n"
    @test_throws InterruptException Corset.run_command(["rules", root], FailingStream(InterruptException()), devnull)
end

@testset "corset: a closed output pipe ends the run quietly" begin
    @test Corset.broken_pipe(Base.IOError("write", Base.UV_EPIPE))
    @test !Corset.broken_pipe(Base.IOError("write", Base.UV_EIO))
    @test !Corset.broken_pipe(ErrorException("other"))
end

@testset "corset: a malformed Project.toml exits with 2" begin
    root = package_tree("name = \n", ["src/Demo.jl" => "module Demo\nend\n"])
    redirect_stderr(devnull) do
        @test captured_main(["rules", root])[2] == 2
    end
end

@testset "corset: missing command or invalid option exits with 2" begin
    redirect_stderr(devnull) do
        @test captured_main(String[])[2] == 2
        @test captured_main(["check", "--format", "invalid"])[2] == 2
    end
end

@testset "a source file that does not parse is a finding and the other files are still checked" begin
    broken = package_tree(
        "name = \"Demo\"\n[preferences.Corset]\ndirectories = [\"src\"]\n",
        SOURCE_TREE ∪ ["src/Broken.jl" => "f(x) = (\n"],
    )
    output, code = captured_main(["check", broken, "--no-load", "--format", "concise"])
    @test code == 1
    @test occursin("[parse-error]", output)
    @test occursin("src/Broken.jl", output)
    @test occursin("[where-return]", output)
end

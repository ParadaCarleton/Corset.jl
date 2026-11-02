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

    @testset "a typo fails loud" begin
        @test_throws ErrorException load_config(
            package_tree(
                "name = \"D\"\n[preferences.Corset]\npedantc = true\n",
                Pair[],
            )
        )
        @test_throws ErrorException load_config(
            package_tree(
                "name = \"D\"\n[preferences.Corset.levels]\nno-such-rule = \"deny\"\n",
                Pair[],
            )
        )
        @test_throws ErrorException load_config(
            package_tree(
                "name = \"D\"\n[preferences.Corset.levels]\nfloat64 = \"loud\"\n",
                Pair[],
            )
        )
        @test_throws ErrorException with_overrides(config, false, ["no-such-rule" => :deny])
    end

    @test_throws ErrorException project_root(mktempdir())
end

@testset "corset: every rule has a unique name and a known group" begin
    names = rule_name.(RULES)
    @test allunique(names)
    @test all(group in (:default, :pedantic) for group in rule_group.(RULES))
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
            [SOURCE_TREE; "base.toml" => "[where-return]\n\"Demo.jl\" = 1\n"],
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

    @testset "where-return handles unbraced where T and unbound arguments" begin
        unbraced = package_tree(
            "name = \"Demo\"\n",
            [
                "src/Demo.jl" => "module Demo\nf(x::T)::T where T = x\ng(x)::T where {T} = convert(T, x)\nend\n",
            ],
        )
        @test length(run_rules(load_config(unbraced), unbraced)[1]) == 2
        findings, _ = run_rules(load_config(unbraced), unbraced; fix = true)
        @test length(findings) == 1
        @test only(findings).rule == "where-return"
        @test occursin("(f(x::T)::T) where T = x", read(joinpath(unbraced, "src", "Demo.jl"), String))
        @test occursin("g(x)::T where {T} = convert(T, x)", read(joinpath(unbraced, "src", "Demo.jl"), String))
    end

    @testset "module rules run on a loaded package" begin
        findings, skipped = run_rules(
            with_overrides(load_config(pkgdir(Corset)), false, ["hidden-input" => :deny]),
            pkgdir(Corset);
            mod = Corset.WorkloadPackage,
            signatures = concrete_signatures(Corset.WorkloadPackage),
        )
        @test ("hidden-input", :deny) in
            [(finding.rule, finding.level) for finding in findings]
        @test isempty(skipped)
    end
end

@testset "corset: output and exit codes" begin
    root = package_tree("name = \"Demo\"\n", SOURCE_TREE)
    findings, _ = run_rules(load_config(root), root)
    human = sprint(print_findings, root, findings, "human")
    @test human == "warn[where-return]: Demo.jl\n  --> src/Demo.jl:2\n"
    @test sprint(print_findings, root, findings, "concise") ==
        "src/Demo.jl:2: warn: [where-return] Demo.jl\n"
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
end

@testset "corset: the command" begin
    root = package_tree("name = \"Demo\"\n", SOURCE_TREE)
    output, code = captured_main(["check", root, "--no-load", "--format", "concise"])
    @test (output, code) == ("src/Demo.jl:2: warn: [where-return] Demo.jl\n", 0)
    @test captured_main(["check", root, "--no-load", "--deny-warnings"])[2] == 1
    @test captured_main(["check", root, "--no-load", "--deny", "where-return"])[2] == 1
    @test captured_main(["check", root, "--no-load", "--allow", "where-return"]) == ("", 0)
    @test occursin("float64", first(captured_main(["rules", root, "--pedantic"])))
    @test captured_main(["check", root, "--no-load", "--allow", "no-such-rule"])[2] == 2
    @test_throws ErrorException Corset.load_package(
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
    smells = join((SNIPPETS[name]["source"] for name in ("nothing-return", "range-guard", "return-type", "concrete-arg", "concrete-return", "float64", "c-type", "ref", "annotation", "one-letter", "jscpd")), "\n")
    write(joinpath(root, "src", "smells.jl"), smells)
    write(joinpath(root, "Project.toml"), "name = \"Demo\"\n")
    config = with_overrides(load_config(root), true, Pair{String, Symbol}[])
    bin = fake_fatou(mktempdir(), "src/smells.jl:3:5: warning[unused-binding] unused\\nchecked 1 file(s): 1 finding\\n")
    path = ENV["PATH"]
    ENV["PATH"] = "$bin:$path"
    try
        findings, skipped = run_rules(config, root; mod = fixture, signatures = concrete_signatures(fixture))
        @test isempty(skipped)
        pedantic = [rule_name(rule) for rule in RULES if rule_group(rule) === :pedantic]
        @test setdiff(pedantic, Set(finding.rule for finding in findings)) == String[]
    finally
        ENV["PATH"] = path
    end
end

@testset "corset: JET sites need the caller's JET" begin
    @test_throws ErrorException Corset.loaded_jet(Dict{Base.PkgId, Module}())
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
    @test_throws DomainError Corset.run_command(["rules", root], FailingStream(DomainError(1)), devnull)
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

# Corset's own tests. Each rule reads deliberately bad code from `fixtures/`, kept out of `.jl`
# files so a linter of this tree does not read it.
using Test: @testset, @test, @test_logs, @test_throws
using JET: JET
using TOML: TOML
using Corset: Corset
using Corset:
    CONCRETE_RETURN_FIX,
    Repository,
    Site,
    ratchet!,
    offenders!,
    @call_sites,
    @opt_sites,
    float64_ops,
    abstract_fields,
    abstract_locals,
    undefined_names,
    boxed_closures,
    c_type_sites,
    capturing_closures,
    concrete_arguments,
    concrete_returns,
    fatou_sites,
    float64_sites,
    hidden_inputs,
    inferred_methods,
    located_source,
    misplaced_imports,
    missing_annotations,
    module_structs,
    nothing_returns,
    one_letter_sites,
    place_imports!,
    present_directories,
    range_guards,
    repeated_prefix,
    repeated_statements,
    repository_sources,
    return_type_calls,
    struct_locations,
    struct_site,
    unmarked_effects,
    fix_where_returns,
    where_return_sites

const FIXTURES = joinpath(@__DIR__, "fixtures")
const SNIPPETS = TOML.parsefile(joinpath(FIXTURES, "snippets.toml"))

"""Write each `name => text` of `files` under `root`, making directories, and return `root`."""
function write_tree(root::AbstractString, files::AbstractVector{<:Pair})::String
    for (name, text) in files
        mkpath(dirname(joinpath(root, name)))
        write(joinpath(root, name), text)
    end
    return root
end

"""The path of `source.jl` holding the snippet of `rule` (`fixtures/snippets.toml`), in a fresh tree."""
snippet_file(rule::AbstractString)::String = joinpath(
    write_tree(mktempdir(), ["source.jl" => SNIPPETS[rule]["source"]]),
    "source.jl",
)

"""The `Site`s that `finder(path, located)` finds in the snippet of `rule`."""
function found_in(finder::Function, rule::AbstractString)::Vector{Site}
    path = snippet_file(rule)
    return finder(path, located_source(path))
end

"""The keys of `sites`."""
site_keys(sites::AbstractVector{Site})::Vector{String} = [site.key for site in sites]

"""The lines of `sites`."""
site_lines(sites::AbstractVector{Site})::Vector{Int} = [site.line for site in sites]

"""A module loaded from `fixtures/fixture_module.txt`, written as `fixture.jl` in the tree `root`."""
function load_fixture(root::AbstractString)::Module
    path = joinpath(
        write_tree(
            root,
            ["fixture.jl" => read(joinpath(FIXTURES, "fixture_module.txt"), String)],
        ),
        "fixture.jl",
    )
    fixture = Module(:Fixture)
    Base.include(fixture, path)
    return fixture
end

"""The files `repository_sources` finds under `src` of `repository`, relative to `root`."""
relative_sources(repository::Repository, root::AbstractString)::Vector{String} = [
    relpath(file, root)
    for file in repository_sources(repository, ("src",))
]

"""Install in `bin` a `fatou` that prints `printed` (a `printf` format) and return `bin`."""
function fake_fatou(bin::AbstractString, printed::AbstractString)::String
    write_tree(bin, ["fatou" => "#!/bin/sh\nprintf '$printed'\n"])
    chmod(joinpath(bin, "fatou"), 0o755)
    return bin
end

"""The text `place_imports!` leaves in `files` (name => text) written into a fresh tree, which then has no misplaced import."""
function placed(files::AbstractVector{<:Pair})::Dict{String, String}
    repository = Repository(write_tree(mktempdir(), files))
    place_imports!(repository, (".",))
    @test isempty(misplaced_imports(repository, (".",)))
    return Dict(
        name => read(joinpath(repository.root, name), String)
        for (name, _) in files
    )
end

@testset "Corset" begin
    @testset "a Repository is strict by default" begin
        repository = Repository(".")
        @test repository.root == abspath(".")
        @test isnothing(repository.baseline)
        @test repository.one_letter_exempt == ()
        @test repository.skipped_directories == ()
    end

    @testset "without a baseline every offender's key is past it" begin
        repository = Repository(mktempdir())
        sites = [Site("first", "", 0), Site("second", "", 0), Site("second", "", 0)]
        @test (
            @test_logs (:error, r"rule: offenders past no baseline") offenders!(
                repository,
                "rule",
                sites,
            )
        ) ==
            ["first", "second"]
        @test ratchet!(repository, "rule", Site[]) == String[]
    end

    @testset "a `# lint:` comment opts its lines out" begin
        text = "one() = 1 # lint: rule\ntwo() = 2\n# lint: rule-begin\nthree() = 3\n# lint: rule-end\nfour() = 4 # lint: other\n"
        root = write_tree(
            mktempdir(),
            ["source.jl" => text, "whole.jl" => "# lint: rule-file\none() = 1\n"],
        )
        sites = [Site("line $line", joinpath(root, "source.jl"), line) for line in 1:6]
        @test offenders!(Repository(root), "rule", sites) == ["line 2", "line 6"]
        @test isempty(offenders!(
            Repository(root),
            "rule",
            [Site("whole", joinpath(root, "whole.jl"), 2)],
        ))
    end

    @testset "with a baseline each key is held to its entry, and entries fall" begin
        root = mktempdir()
        baseline = joinpath(root, "baseline.toml")
        write(baseline, "")
        repository = Repository(root; baseline)
        sites = [Site("counted", "", 0), Site("counted", "", 0), Site("noted", "", 0)]
        @test isempty(@test_logs (:warn, r"seeded") offenders!(repository, "rule", sites))
        @test TOML.parsefile(baseline)["rule"] == Dict("counted" => 2, "noted" => 1)
        write(baseline, "[rule]\ncounted = 2\nnoted = \"kept: deliberate\"\n")
        @test isempty(offenders!(repository, "rule", [sites; Site("noted", "", 0)]))
        @test offenders!(repository, "rule", [sites; Site("counted", "", 0)]) == ["counted"]
        @test offenders!(repository, "rule", [Site("fresh", "", 0)]; scopes = ("noted",)) ==
            ["fresh"]
        @test TOML.parsefile(baseline)["rule"] == Dict("counted" => 2)
        @test ratchet!(repository, "rule", [Site("counted", "", 0)]) == String[]
        @test TOML.parsefile(baseline)["rule"] == Dict("counted" => 1)
    end

    @testset "repository_sources skips hidden directories, and skipped ones when asked" begin
        root = write_tree(
            mktempdir(),
            [
                "src/a.jl" => "",
                "src/vendor/b.jl" => "",
                "src/.hidden/c.jl" => "",
                "src/notes.txt" => "",
            ],
        )
        @test relative_sources(Repository(root), root) == ["src/a.jl", "src/vendor/b.jl"]
        @test relative_sources(Repository(root; skipped_directories = ("vendor",)), root) ==
            ["src/a.jl"]
        @test present_directories(Repository(root), ("src", "missing")) == ("src",)
    end

    root = mktempdir()
    fixture = load_fixture(root)
    repository = Repository(root)
    inferred = inferred_methods(fixture)

    @testset "hidden-input: a read of a mutable or non-constant global" begin
        @test unique(site_keys(hidden_inputs(fixture))) == ["counter"]
    end

    @testset "abstract-local: a local variable that infers no concrete type" begin
        @test site_keys(abstract_locals(repository, inferred)) ==
            ["fixture.jl abstract_local"]
        @test isempty(abstract_locals(Repository(mktempdir()), inferred))
    end

    @testset "bang: a function that always returns nothing has a name ending in !" begin
        @test site_keys(unmarked_effects(repository, inferred)) == ["fixture.jl announce"]
    end

    @testset "closure: closures that capture data, and those holding a Core.Box" begin
        sites = Dict(site.key => site for site in capturing_closures(fixture))
        @test Set(keys(sites)) ==
            Set(["fixture.jl adder", "fixture.jl boxed", "fixture.jl lineless"])
        @test site_keys(boxed_closures(fixture)) == ["fixture.jl boxed"]
        @testset "a closure built without line numbers sits at the function that creates it" begin
            fixture_lines = readlines(joinpath(root, "fixture.jl"))
            @test sites["fixture.jl lineless"].line ==
                findfirst(startswith("@eval function lineless"), fixture_lines)
            @test sites["fixture.jl lineless"].file == joinpath(root, "fixture.jl")
        end
    end

    @testset "abstract-field, repeated-prefix: struct fields" begin
        structs = Dict(nameof(type) => type for type in module_structs(fixture))
        @test Set(keys(structs)) == Set([:Holder, :Plain, :SolverControls, :Tally])
        @test nameof.(Corset.mutable_structs(fixture)) == [:Tally]
        @test abstract_fields(structs[:Holder]) == [:held]
        @test isempty(abstract_fields(structs[:Plain]))
        @test repeated_prefix(structs[:SolverControls]) == "solver"
        @test isnothing(repeated_prefix(structs[:Plain]))
        path = joinpath(root, "fixture.jl")
        @test struct_site(:Holder, struct_locations([path])) ==
            Site("Holder", path, findfirst(==("struct Holder"), readlines(path)))
    end

    @testset "a struct is placed at its `struct` line, below its docstring" begin
        path = snippet_file("struct-line")
        lines = readlines(path)
        locations = struct_locations([path])
        @test locations ==
            Dict(
                :Documented => (path, findfirst(startswith("struct Documented"), lines)),
                :Counter => (path, findfirst(endswith("struct Counter"), lines)),
                :Plain => (path, findfirst(startswith("struct Plain"), lines)),
                Symbol("Odd Name") => (
                    path,
                    findfirst(startswith("struct var\"Odd Name\""), lines),
                ),
            )
        sites = [struct_site(name, locations) for name in (:Documented, :Counter)]
        @test offenders!(Repository(dirname(path)), "wide-struct", sites) == ["Counter"]
    end

    @testset "jet: JET reports as sites" begin
        errors = Site[]
        @call_sites "error analysis" errors target_modules = (fixture,) fixture.broken(1)
        @test !isempty(errors)
        @test all(site -> startswith(site.key, "error analysis: broken"), errors)
        dispatches = Site[]
        @opt_sites "optimization analysis" dispatches target_modules = (
            fixture,
        ) fixture.unstable(fixture.make_box())
        @test !isempty(dispatches)
        clean = Site[]
        @call_sites "error analysis" clean target_modules = (fixture,) fixture.reads_limit(
            1,
        )
        @test isempty(clean)
    end

    @testset "float64_ops: Float64 operations in optimized IR" begin
        @test float64_ops(fixture.widened, (Float32,)) > 0
        @test float64_ops(fixture.narrow, (Float32,)) == 0
    end

    @testset "nothing-return: a declared Union{Nothing, …} result" begin
        @test site_keys(found_in(nothing_returns, "nothing-return")) == ["maybe"]
    end

    @testset "range-guard: floatmin, floatmax, exp's range edge, isfinite of exp" begin
        @test site_keys(found_in(range_guards, "range-guard")) ==
            ["guard", "edge", "finite"]
    end

    @testset "repeated-statement: a statement repeated in one block" begin
        sites = found_in(repeated_statements, "repeated-statement")
        @test length(sites) == 1
        @test startswith(only(sites).key, "twice: ")
        @test only(sites).line == 3
    end

    @testset "return-type: Core.Compiler.return_type" begin
        @test site_lines(found_in(return_type_calls, "return-type")) == [1]
    end

    @testset "concrete-arg: an argument annotated with a concrete container it does not resize" begin
        @test site_lines(found_in(concrete_arguments, "concrete-arg")) == [1]
    end

    @testset "concrete-return: a result annotated with a concrete type, `Matrix{T}` included" begin
        sites = found_in(
            (path, located) -> concrete_returns(path, located, Base),
            "concrete-return",
        )
        @test site_keys(sites) == ["source.jl fixed", "source.jl squared"]
        logged = (:error, Regex("Fix: \\Q$CONCRETE_RETURN_FIX\\E"))
        @test (
            @test_logs logged offenders!(
                Repository(mktempdir()),
                "concrete-return",
                sites;
                fix = CONCRETE_RETURN_FIX,
            )
        ) ==
            site_keys(sites)
    end

    @testset "float64: Float64 tokens and untyped float literals" begin
        @test site_lines(float64_sites(snippet_file("float64"))) == [1, 1]
    end

    @testset "c-type: C-interop types outside a ccall" begin
        @test site_lines(c_type_sites(snippet_file("c-type"))) == [1, 1]
    end

    @testset "ref: Ref and RefValue outside a ccall" begin
        @test site_lines(Corset.ref_sites(snippet_file("ref"))) == [1, 2, 5]
    end

    @testset "annotation: every argument and result annotated" begin
        @test site_keys(found_in(missing_annotations, "annotation")) ==
            ["source.jl untyped", "source.jl no_result"]
    end

    @testset "one-letter: one-letter variable names, with exemptions opt-in" begin
        path = snippet_file("one-letter")
        @test length(one_letter_sites(Repository(dirname(path)), path)) == 2
        @test length(one_letter_sites(
            Repository(dirname(path); one_letter_exempt = (:p,)),
            path,
        )) ==
            1
    end

    @testset "fatou: findings of `fatou lint`" begin
        tree = write_tree(mktempdir(), ["source.jl" => "one() = 1\n"])
        bin = fake_fatou(
            mktempdir(),
            "source.jl:3:5: warning[unused-binding] unused\\nchecked 1 file(s): 1 finding\\n",
        )
        path = ENV["PATH"]
        ENV["PATH"] = "$bin:$path"
        try
            @test fatou_sites(Repository(tree), (".",)) ==
                [Site("source.jl unused-binding", joinpath(tree, "source.jl"), 3)]
            fake_fatou(bin, "checked 1 file(s): clean\\n")
            @test isempty(fatou_sites(Repository(tree), (".",)))
            fake_fatou(bin, "source.jl: parse error\\n")
            @test_throws ErrorException fatou_sites(Repository(tree), (".",))
            ENV["PATH"] = string(mktempdir())
            @test_throws ErrorException fatou_sites(Repository(tree), (".",))
        finally
            ENV["PATH"] = path
        end
    end

    @testset "misplaced-import: imports sit in the files that use them" begin
        snippets = SNIPPETS["misplaced-import"]
        tree = write_tree(
            mktempdir(),
            ["main.jl" => snippets["main"], "child.jl" => snippets["child"]],
        )
        @test site_keys(misplaced_imports(Repository(tree), (".",))) ==
            ["main.jl a", "main.jl c", "main.jl D"]
        place_imports!(Repository(tree), (".",))
        @test isempty(misplaced_imports(Repository(tree), (".",)))
        @testset "an import no file uses is deleted, one only an included file uses moves there" begin
            @test read(joinpath(tree, "main.jl"), String) ==
                "module Main1\nusing A: b\ninclude(\"child.jl\")\nf() = b\nend\n"
        end
        @testset "a `using M: a, b` list splits across files; a name both files use stays put" begin
            @test read(joinpath(tree, "child.jl"), String) ==
                "using A: a\nusing C: c\ng() = a + b + c\n"
        end
        @testset "an opted-out import and a bare `using` stay" begin
            kept_tree = write_tree(mktempdir(), ["kept.jl" => snippets["kept"]])
            place_imports!(Repository(kept_tree), (".",))
            @test read(joinpath(kept_tree, "kept.jl"), String) == snippets["kept"]
        end
    end

    @testset "misplaced-import: a name used only in a command interpolation counts as used" begin
        tree = write_tree(
            mktempdir(),
            [
                "cmd.jl" =>
                    "using A: a\nusing B: b\nusing C: c\nf() = `echo \$(a.x()) \$b \\\$c`\n",
            ],
        )
        @test site_keys(misplaced_imports(Repository(tree), (".",))) == ["cmd.jl c"]
        @testset "a `\$` inside single quotes is shell text, not an interpolation" begin
            quoted = write_tree(
                mktempdir(),
                ["cmd.jl" => "using A: a\nf() = `bash -c 'echo \"\$@\" \$a' x`\n"],
            )
            @test site_keys(misplaced_imports(Repository(quoted), (".",))) == ["cmd.jl a"]
        end
    end

    @testset "hidden-input: a regex constant is not state; a global stream is" begin
        @test !Corset.is_hidden_input(GlobalRef(Corset, :OPT_OUT))
        @test Corset.is_hidden_input(GlobalRef(Base, :stdout))
    end

    @testset "abstract-local: a homogeneous variadic tuple is concrete in use, a bare Tuple is not" begin
        @test !Corset.abstract_local_type(Tuple{Vararg{String}})
        @test Corset.abstract_local_type(Tuple)
        @test Corset.abstract_local_type(Tuple{Vararg{Real}})
    end
end

@testset "short-form `where` binds the method, not the return annotation" begin
    @test fix_where_returns("f(x::V{E})::Vector{E} where {E<:Real} = x\n") ==
        "(f(x::V{E})::Vector{E}) where {E<:Real} = x\n"
    @test fix_where_returns("f(x::V{E}, 1)::Vector{E} where {E} = x\n") ==
        "(f(x::V{E}, 1)::Vector{E}) where {E} = x\n"
    @testset "no argument uses the variable, so the annotation may be deliberate" begin
        kept = "g()::Vector{T} where {T} = T[]\n"
        @test fix_where_returns(kept) == kept
    end
    @testset "the long form and a method-level `where` are left alone" begin
        for kept in (
                "function f(x::V{E})::Vector{E} where {E}\n    x\nend\n",
                "f(x::V{E}) where {E} = x\n",
                "(f(x::V{E})::Vector{E}) where {E} = x\n",
            )
            @test fix_where_returns(kept) == kept
            path = tempname()
            write(path, kept)
            @test isempty(where_return_sites(path))
        end
    end
end

@testset "a script without a module keeps the imports its included files use" begin
    result = placed([
        "main.jl" => "using A: a\ninclude(\"child.jl\")\n",
        "child.jl" => "g() = a\n",
    ])
    @test result["child.jl"] == "using A: a\ng() = a\n"
end

@testset "annotation rules" begin
    check(text::String, rule::Function) = (
        path = tempname() * ".jl";
        write(path, text);
        rule(path, located_source(path))
    )
    @testset "a keyword splat needs no annotation, and Bool is an allowed result" begin
        text = "f(x::T; options...)::Bool where {T} = true\n"
        @test isempty(check(text, missing_annotations))
        @test isempty(check(text, (path, located) -> concrete_returns(path, located, Main)))
    end
    @testset "a positional argument still needs one" begin
        @test length(check("f(x)::Bool = true\n", missing_annotations)) == 1
    end
end

@testset "concrete-return: a package struct parameterized by a `where` variable is generic" begin
    scope = Module(:ReturnScope)
    Core.eval(
        scope,
        :(
            struct Wrapped{E}
                inner::E
            end
        ),
    )
    Core.eval(
        scope,
        :(
            struct Set{E}
                inner::E
            end
        ),
    )
    check(text::String) = (
        path = tempname() * ".jl";
        write(path, text);
        length(concrete_returns(path, located_source(path), scope))
    )
    @test check("(wrap(element::E)::Wrapped{E}) where {E} = Wrapped(element)\n") == 0
    @test check("(wrap(element::E)::Set{E}) where {E} = Set(element)\n") == 0
    @test check("(wrap(element::E)::Wrapped{E}) where {E <: Real} = Wrapped(element)\n") ==
        0
    @test check(
        "function wrap(element::E)::Wrapped{E} where {E}\n    return Wrapped(element)\nend\n",
    ) ==
        0
    @test check(
        "(wrap(elements::AbstractVector{E})::Wrapped{Vector{E}}) where {E} = Wrapped(collect(elements))\n",
    ) ==
        0
    @test check(
        "(wrap(element::E)::Union{Nothing, Wrapped{E}}) where {E} = Wrapped(element)\n",
    ) ==
        0
    @test check("wrap(element::Float32)::Wrapped{Float32} = Wrapped(element)\n") == 1
    @test check("wrap(element::Float32)::Wrapped = Wrapped(element)\n") == 1
    @test check("(wrap(element::Float32)::Wrapped{E}) where {T} = Wrapped(element)\n") == 1
    @test check("(listed(element::E)::Vector{E}) where {E} = [element]\n") == 1
end

@testset "a name used only inside a macro call counts as used" begin
    result = placed([
        "main.jl" => "using A: a\ninclude(\"child.jl\")\n",
        "child.jl" => "@testset \"x\" begin\n    @test f(a(2))\nend\n",
    ])
    @test result["child.jl"] == "using A: a\n@testset \"x\" begin\n    @test f(a(2))\nend\n"
end

@testset "import placement reads every include form and import shape" begin
    @testset "a moved import joins the imports the target file already has, at their indent" begin
        result = placed([
            "main.jl" => "using A: a\ninclude(\"child.jl\")\n",
            "child.jl" => "using C: c\ng() = a + c\n",
        ])
        @test result["child.jl"] == "using C: c\nusing A: a\ng() = a + c\n"
        result = placed([
            "main.jl" => "module M\n    using A: a\n    include(\"child.jl\")\nend\n",
            "child.jl" => "    using C: c\n    g() = a + c\n",
        ])
        @test result["child.jl"] == "    using C: c\n    using A: a\n    g() = a + c\n"
    end
    @testset "an import has nowhere to go in a module without imports" begin
        @test_throws ErrorException placed([
            "main.jl" => "using A: a\ninclude(\"child.jl\")\n",
            "child.jl" => "module Inner\ng() = a\nend\n",
        ])
    end
    @testset "an unused import sharing its line with code is cut out of the line" begin
        @test placed(["main.jl" => "module M; using A: a; f() = 1; end\n"])["main.jl"] ==
            "module M; ; f() = 1; end\n"
    end
    @testset "aliases, macros and string macros are names" begin
        @test placed([
            "main.jl" => "using A: a as b, @m\nf() = b\ng() = raw\"x\"\n",
        ])["main.jl"] ==
            "using A: a as b\nf() = b\ng() = raw\"x\"\n"
    end
    @testset "include paths: joinpath with @__DIR__ is followed, anything else blocks the move" begin
        files = [
            "main.jl" => "using A: a\ninclude(joinpath(@__DIR__, \"child.jl\"))\n",
            "child.jl" => "g() = a\n",
        ]
        @test placed(files)["child.jl"] == "using A: a\ng() = a\n"
        for blocked in (
                "include(\"gone.jl\")",
                "include(name)",
                "include(string(\"child.jl\"))",
                "include(\"child.jl\", 1)",
            )
            kept = "using A: a\n$blocked\n"
            @test placed(["main.jl" => kept, "child.jl" => "g() = a\n"])["main.jl"] == kept
        end
        cyclic = placed([
            "main.jl" => "using A: a\ninclude(\"child.jl\")\n",
            "child.jl" => "include(\"child.jl\")\ng() = a\n",
        ])
        @test cyclic["main.jl"] == "include(\"child.jl\")\n"
    end
end

module Shapes
    struct Callable end
    struct Left end
    struct Right end
    struct Control
        step_size::Int
        step_count::Int
        step_limit::Int
    end
    (callable::Callable)(argument::Any) = argument
end

@testset "rule helpers read every shape of input" begin
    @testset "a callee is the type its method is called on, through a type variable bound" begin
        @test Corset.callee_name(only(methods(Shapes.Callable()))) === Shapes.Callable.name
        @test Corset.callee_name(TypeVar(:T, Shapes.Callable)) === Shapes.Callable.name
        @test Corset.callee_name(Vector) === Vector.body.name
        @test isnothing(Corset.callee_name(Union{Shapes.Left, Shapes.Right}))
    end
    @testset "a missing binding hides no input" begin
        @test !Corset.is_hidden_input(GlobalRef(Main, :no_such_binding_anywhere))
    end
    @testset "abstract local types: unions, containers, tuples and Type" begin
        concrete = (
            Union{},
            Union{Int, String},
            Type{Int},
            Vector{Int},
            Dict{String, Int},
            Tuple{Int, Float64},
            Tuple{Vararg{Int}},
        )
        @test !any(Corset.abstract_local_type, concrete)
        @test Corset.abstract_local_type(Union{Int, Float64, String, Char, Symbol})
        for element in (Any, Number)
            @test Corset.abstract_local_type(element)
            @test Corset.abstract_local_type(Union{Int, element})
            @test Corset.abstract_local_type(Vector{element})
            @test Corset.abstract_local_type(Dict{String, element})
            @test Corset.abstract_local_type(Tuple{Int, element})
            @test Corset.abstract_local_type(Tuple{Vararg{element}})
            @test Corset.holds_abstract(Tuple{element})
        end
    end
    @testset "declared field types: abstract at any depth" begin
        @test Corset.holds_abstract(Vector{Vector})
        @test !Corset.holds_abstract(Vector{Int})
    end
    @testset "a word shared by most fields is the prefix the type should say once" begin
        @test Corset.repeated_prefix(Shapes.Control) == "step"
    end
    @testset "nodes of another kind are no range guard and call no exp" begin
        @test !Corset.is_range_guard(:name)
        @test !Corset.calls_exp(:name)
    end
    @testset "a definition without a body marker starts at the line it was found" begin
        @test Corset.definition_line(Expr(:call, :f), 7) == 7
    end
    @testset "a testset names the code inside it" begin
        @test Corset.testset_name(Meta.parse("@testset \"a b\" begin end")) ===
            Symbol("a b")
        @test isnothing(Corset.testset_name(Meta.parse("@testset begin end")))
        path = tempname() * ".jl"
        write(path, "@testset \"inside\" begin\n    f(a) = 1\nend\n")
        @test any(item.enclosing === :inside for item in located_source(path))
    end
    @testset "concrete containers: bare, in a Union, and not a type at all" begin
        @test Corset.is_concrete_container(Meta.parse("Union{Vector, Nothing}"))
        @test !Corset.is_concrete_container(Meta.parse("a.b"))
        @test !Corset.is_concrete_container(1)
    end
    @testset "annotated arguments: keyword, keyword-section and splat forms" begin
        @test Corset.annotated_arguments(Expr(:kw, :(x::Int), 1)) == [(:x, :Int)]
        @test Corset.annotated_arguments(Expr(:parameters, :(k::Int))) == [(:k, :Int)]
        @test Corset.annotated_arguments(Expr(:parameters, Expr(:kw, :(k::Int), 1))) ==
            [(:k, :Int)]
        @test Corset.annotated_arguments(Expr(:..., :(rest::Int))) == [(:rest, :Int)]
        @test isempty(Corset.annotated_arguments(Expr(:parameters, :plain)))
    end
    @testset "result types: unknown names, literals and non-types are no package struct" begin
        @test !Corset.package_type(:NoSuchTypeAnywhere, Main)
        @test !Corset.package_type(1, Main)
        @test !Corset.mentions_variable(1, (:E,))
        @test isnothing(Corset.type_head(Meta.parse("a.b")))
        @test isnothing(Corset.type_head(1))
        @test !Corset.constructs_own_type(:(x = 1))
    end
    @testset "untyped arguments: defaults and literals" begin
        @test Corset.untyped_argument(Expr(:kw, :x, 1))
        @test !Corset.untyped_argument(1)
    end
    @testset "bound names: defaults, tuples and field targets" begin
        @test Corset.bound_names(Expr(:kw, :x, 1)) == [:x]
        @test Corset.bound_names(Expr(:tuple, :a, :b)) == [:a, :b]
        @test isempty(Corset.bound_names(Meta.parse("a.b")))
        @test Corset.one_letter_names(Meta.parse("try\n1\ncatch e\n2\nend"), ()) == [:e]
    end
end

@testset "closure reflection follows nested closures and macro-made code" begin
    closure_chain = Module(:ClosureChain)
    Base.include(closure_chain, joinpath(FIXTURES, "closure_module.txt"))
    defined = Corset.defined_methods(closure_chain)
    namers = Corset.closure_namers(closure_chain, defined)
    @testset "a nested closure is defined by the function that holds the outermost one" begin
        @test Set(Corset.closure_definer(name, namers).name for name in keys(namers)) ==
            Set([:nested, :recursive, :twice])
        @test length(Corset.live_closures(closure_chain, defined)) == length(namers)
    end
    @testset "code from a macro sits at the method's line, and a bare argument slot too" begin
        method = only(methods(closure_chain.uses_macro))
        code = Corset.lowered(method)
        @test any(
            index -> Corset.statement_line(code, method, index) == method.line,
            eachindex(code.code),
        )
        @test Corset.slot_line(Corset.Inferred(method, code, false), 2) == method.line
    end
    @testset "a builtin has no lowered code and returns no argument's call" begin
        @test isnothing(Corset.lowered(first(methods(Core.tuple))))
        @test isempty(Corset.created_closures(first(methods(Core.tuple)), Corset))
        @test !Corset.returns_argument_call(first(methods(Core.tuple)))
    end
end

module Probe
    function generic(point::AbstractVector{E})::E where {E <: Real}
        total = zero(E)
        for entry in point
            total += entry
        end
        return total
    end
    off(::Nothing)::Nothing = nothing
    off(value::Real)::typeof(value) = value
    function catches()::Nothing
        try
            error("probe")
        catch exception
            return nothing
        end
    end
    __init__()::Nothing = nothing
    function each_part(body::B, parts::Integer)::Nothing where {B}
        foreach(body, 1:parts)
        return nothing
    end
    struct Buffer{E <: Real}
        entries::Vector{E}
    end
    function Buffer(point::AbstractVector{E}, extra::Integer)::Buffer{E} where {E <: Real}
        entries = Vector{E}(undef, length(point) + extra)
        return Buffer(entries)
    end
    function matches(texts::AbstractVector{<:AbstractString})::Int
        positions = findall(==("x"), texts)
        return length(positions)
    end
    function passing(thunk::F) where {F}
        try
            return thunk()
        catch exception
            rethrow(exception)
        end
    end
end

@testset "abstract locals and bang names read what ran" begin
    Probe.generic(Float32[1, 2])
    Probe.off(nothing)
    Probe.off(1.0f0)
    Probe.catches()
    Probe.__init__()
    Probe.each_part(identity, 2)
    Probe.each_part(string, 2)
    Probe.passing(() -> nothing)
    Probe.matches(["x", "y"])
    Probe.Buffer(Float32[1, 2], 1)
    repository = Repository(@__DIR__)
    inferred = inferred_methods(Probe)
    @testset "a generic method or constructor is typed at the types it was called with, and a catch variable is skipped" begin
        @test isempty(abstract_locals(repository, inferred))
    end
    @testset "a nothing method beside a valued one is not a procedure; a lone one is" begin
        keys = [site.key for site in unmarked_effects(repository, inferred)]
        @test !any(contains("off"), keys)
        @test any(contains("catches"), keys)
        @test !any(contains("__init__"), keys)
    end
    @testset "a generic procedure called with several types is one site" begin
        keys = [site.key for site in unmarked_effects(repository, inferred)]
        @test count(contains("each_part"), keys) == 1
    end
    @testset "a method returning a call to its argument gets no verdict from what its callers passed" begin
        @test !any(
            contains("passing"),
            [site.key for site in unmarked_effects(repository, inferred)],
        )
    end
end

include("cli.jl")

@testset "undefined_names: a name nothing defines is reported, and so is an unlowered testset" begin
    write_scan(text::AbstractString)::String = joinpath(
        write_tree(mktempdir(), ["scan.jl" => text]),
        "scan.jl",
    )
    planted = write_scan("@testset \"f\" begin\n x = 1\n @test x + absent_name == 2\nend\n")
    unresolved, unlowered = undefined_names(planted; scope = @__MODULE__)
    @test unresolved == ["line 1: `absent_name`"]
    @test isempty(unlowered)
    near_miss = write_scan("@testset \"f\" begin\n x = 1\n @test x + x == 2\nend\n")
    @test undefined_names(near_miss; scope = @__MODULE__) == (String[], String[])
    # A name the file defines, imports or takes from an include is defined; a `@changeprecision` wrapper is entered.
    defined = write_scan(
        "using Test: @test\nhelper(x) = x\n@changeprecision Float32 @testset \"f\" begin\n @test helper(1) == 1\nend\n",
    )
    @test first(undefined_names(defined; scope = @__MODULE__)) == String[]
    root = write_tree(
        mktempdir(),
        [
            "included.jl" => "from_include() = 1\n",
            "main.jl" =>
                "include(\"included.jl\")\n@testset \"f\" begin\n @test from_include() == 1\n @test missing_one == 2\nend\n",
        ],
    )
    @test first(undefined_names(joinpath(root, "main.jl"); scope = @__MODULE__)) ==
        ["line 2: `missing_one`"]
    # A testset whose macro cannot expand here is unscanned, and says so.
    broken = write_scan("@testset \"f\" begin\n @no_such_macro 1\nend\n")
    @test undefined_names(broken; scope = @__MODULE__)[2] == ["line 1"]
    # Testsets inside `let`/`begin` are found; `as` aliases and declared types are defined.
    nested = write_scan(
        "using Test: @test\nimport Base: sum as total\nstruct Box end\nabstract type Shape end\n" *
            "let\n @testset \"f\" begin\n @test total([1]) == 1\n @test Box() isa Box\n @test Shape isa Type\n @test gone == 1\n end\nend\n",
    )
    @test first(undefined_names(nested; scope = @__MODULE__)) == ["line 6: `gone`"]
    # Includes nest, resolve against the includer's directory, and a cycle ends.
    deep = write_tree(
        mktempdir(),
        [
            "sub/inner.jl" => "include(\"leaf.jl\")\ninclude(\"inner.jl\")\n",
            "sub/leaf.jl" => "leaf_name() = 1\n",
            "main.jl" =>
                "include(joinpath(@__DIR__, \"sub\", \"inner.jl\"))\n@testset \"f\" begin\n @test leaf_name() == 1\nend\n",
        ],
    )
    @test first(undefined_names(joinpath(deep, "main.jl"); scope = @__MODULE__)) == String[]
    # `where` signatures define functions; a `#` inside a name is no excuse; self-includes through `..` end.
    where_scan = write_scan(
        "f(x::T) where {T} = x\n@testset \"f\" begin\n @test f(1) == 1\n @test var\"gone#name\" == 1\nend\n",
    )
    @test first(undefined_names(where_scan; scope = @__MODULE__)) == ["line 2: `gone#name`"]
    loop = write_tree(
        mktempdir(),
        [
            "sub/inner.jl" =>
                "include(joinpath(@__DIR__, \"..\", \"sub\", \"inner.jl\"))\n",
            "main.jl" => "include(joinpath(@__DIR__, \"sub\", \"inner.jl\"))\n",
        ],
    )
    @test undefined_names(joinpath(loop, "main.jl"); scope = @__MODULE__) ==
        (String[], String[])
    # Imports of whole modules, destructuring, `where` return types, parametric structs and body imports are all definitions.
    forms = write_scan(
        "using Corset\nimport Test\nusing NoSuchModuleAnywhere\nleft, right = 1, 2\n" *
            "function typed(x::T)::Int where {T}\n 1\nend\nstruct Wrapped{T} <: Any end\n" *
            "@testset \"f\" begin\n using Test: @test\n @test typed(left) + right == 3\n @test Wrapped{Int} isa Type\n" *
            " @test Test.detect_ambiguities isa Function && undefined_names isa Function\n @test include(joinpath(@__DIR__, left)) == 1\nend\n",
    )
    @test first(undefined_names(forms; scope = @__MODULE__)) == String[]
    # An include argument that is not a literal path is never evaluated.
    marker = joinpath(mktempdir(), "ran")
    lazy = write_scan(
        "include(write($(repr(marker)), \"x\") |> string)\n@testset \"f\" begin\n @test 1 == 1\nend\n",
    )
    undefined_names(lazy; scope = @__MODULE__)
    @test !isfile(marker)
end

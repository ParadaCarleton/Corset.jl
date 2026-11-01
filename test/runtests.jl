# Corset's own tests. Each rule reads deliberately bad code from `fixtures/`, kept out of `.jl`
# files so a linter of this tree does not read it.
using Test: @testset, @test, @test_logs, @test_throws
using JET: JET
using TOML: TOML
using Corset: Corset
using Corset: CONCRETE_RETURN_FIX, Repository, Site, ratchet!, offenders!, @call_sites, @opt_sites, float64_ops, undefined_names, abstract_fields, abstract_locals,
    c_type_sites, impure_anonymous_functions, concrete_arguments, concrete_returns, fatou_sites, float64_sites, hidden_inputs,
    inferred_methods, jscpd_sites, located_source, misplaced_imports, missing_annotations, module_structs, non_public_accesses, nothing_returns,
    one_letter_sites, place_imports!, present_directories, range_guards, repeated_prefix, repeated_statements,
    repository_sources, return_type_calls, struct_locations, struct_site, unmarked_effects, fix_where_returns,
    where_return_sites, entry_frames, frame_callees, mentions_module, invoked_instance, logging_call, runtime_dispatches,
    widened_returns, compiled_concretely

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
snippet_file(rule::AbstractString)::String = joinpath(write_tree(mktempdir(), ["source.jl" => SNIPPETS[rule]["source"]]), "source.jl")

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
    path = joinpath(write_tree(root, ["fixture.jl" => read(joinpath(FIXTURES, "fixture_module.txt"), String)]), "fixture.jl")
    fixture = Module(:Fixture)
    Base.include(fixture, path)
    return fixture
end

"""The signatures of the methods of `mod` whose argument types are all concrete: a fixed workload that needs no call."""
concrete_signatures(mod::Module)::Vector{Type} = Type[method.sig for method in Corset.module_methods(mod) if Base.isdispatchtuple(method.sig)]

"""The files `repository_sources` finds under `src` of `repository`, relative to `root`."""
relative_sources(repository::Repository, root::AbstractString)::Vector{String} = [relpath(file, root) for file in repository_sources(repository, ("src",))]

"""The text `place_imports!` leaves in `files` (name => text) written into a fresh tree, which then has no misplaced import."""
function placed(files::AbstractVector{<:Pair})::Dict{String, String}
    repository = Repository(write_tree(mktempdir(), files))
    place_imports!(repository, (".",))
    @test isempty(misplaced_imports(repository, (".",)))
    return Dict(name => read(joinpath(repository.root, name), String) for (name, _) in files)
end

"""A module of `count` structs, each one field wider than the last, and `count` functions returning a capturing closure."""
function generated_module(count::Integer)::Module
    generated = Module(:Generated)
    for index in 1:count
        Core.eval(
            generated, :(
                struct $(Symbol(:Shape, index))
                    $([Symbol(:shape_field, field) for field in 1:index]...)
                end
            )
        )
        Core.eval(generated, :($(Symbol(:maker, index))(offset::Int) = shift::Int -> offset + shift))
    end
    return generated
end

"""Every reflection the module rules make on `mod`."""
function reflect_all(mod::Module)::Nothing
    structs = module_structs(mod)
    Corset.defined_methods(mod)
    abstract_fields.(structs)
    repeated_prefix.(structs)
    impure_anonymous_functions(mod)
    return nothing
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
        sites = [Site("first", "", 0, ""), Site("second", "", 0, ""), Site("second", "", 0, "")]
        @test (@test_logs (:error, r"rule: offenders past no baseline") offenders!(repository, "rule", sites)) == ["first", "second"]
        @test ratchet!(repository, "rule", Site[]) == String[]
        described = [Site("first", "", 0, "local `x`::Any"), Site("first", "", 0, "local `y`::Any"), Site("second", "", 0, "")]
        @test (@test_logs (:error, r"first = 2 \(local `x`::Any; local `y`::Any\)\nsecond = 1\n?$") offenders!(repository, "rule", described)) == ["first", "second"]
    end

    @testset "a `# lint:` comment opts its lines out" begin
        text = "one() = 1 # lint: rule\ntwo() = 2\n# lint: rule-begin\nthree() = 3\n# lint: rule-end\nfour() = 4 # lint: other\n"
        root = write_tree(mktempdir(), ["source.jl" => text, "whole.jl" => "# lint: rule-file\none() = 1\n"])
        sites = [Site("line $line", joinpath(root, "source.jl"), line, "") for line in 1:6]
        @test offenders!(Repository(root), "rule", sites) == ["line 2", "line 6"]
        @test isempty(offenders!(Repository(root), "rule", [Site("whole", joinpath(root, "whole.jl"), 2, "")]))
    end

    @testset "with a baseline each key is held to its entry, and entries fall" begin
        root = mktempdir()
        baseline = joinpath(root, "baseline.toml")
        write(baseline, "")
        repository = Repository(root; baseline)
        sites = [Site("counted", "", 0, ""), Site("counted", "", 0, ""), Site("noted", "", 0, "")]
        @test isempty(@test_logs (:warn, r"seeded") offenders!(repository, "rule", sites))
        @test TOML.parsefile(baseline)["rule"] == Dict("counted" => 2, "noted" => 1)
        write(baseline, "[rule]\ncounted = 2\nnoted = \"kept: deliberate\"\n")
        @test isempty(offenders!(repository, "rule", [sites; Site("noted", "", 0, "")]))
        @test offenders!(repository, "rule", [sites; Site("counted", "", 0, "")]) == ["counted"]
        @test offenders!(repository, "rule", [Site("fresh", "", 0, "")]; scopes = ("noted",)) == ["fresh"]
        @test TOML.parsefile(baseline)["rule"] == Dict("counted" => 2)
        @test ratchet!(repository, "rule", [Site("counted", "", 0, "")]) == String[]
        @test TOML.parsefile(baseline)["rule"] == Dict("counted" => 1)
    end

    @testset "repository_sources skips hidden directories, and skipped ones when asked" begin
        root = write_tree(mktempdir(), ["src/a.jl" => "", "src/vendor/b.jl" => "", "src/.hidden/c.jl" => "", "src/notes.txt" => ""])
        @test relative_sources(Repository(root), root) == ["src/a.jl", "src/vendor/b.jl"]
        @test relative_sources(Repository(root; skipped_directories = ("vendor",)), root) == ["src/a.jl"]
        @test present_directories(Repository(root), ("src", "missing")) == ("src",)
    end

    root = mktempdir()
    fixture = load_fixture(root)
    repository = Repository(root)
    inferred = inferred_methods(fixture, concrete_signatures(fixture))

    @testset "hidden-input: a read of a mutable or non-constant global" begin
        @test unique(site_keys(hidden_inputs(fixture))) == ["counter"]
    end

    @testset "non-public-access: a qualified access or explicit import of a non-public name" begin
        path = joinpath(write_tree(mktempdir(), ["access.jl" => read(joinpath(FIXTURES, "access_module.txt"), String)]), "access.jl")
        access = Module(:Access)
        Base.include(access, path)
        sites = non_public_accesses(access)
        @test site_keys(sites) == ["Base.JuliaSyntax", "Base.JuliaSyntax", "Base.uniontypes"]
        @test site_lines(sites) == [3, 7, 1]
        @test first(sites).detail == "`JuliaSyntax` is not public in `Base`"
        offending = @test_logs (:info, r"1 site\(s\) opted out") (:error, r"Base\.JuliaSyntax = 1 ") offenders!(Repository(dirname(path)), "non-public-access", sites)
        @test offending == ["Base.JuliaSyntax", "Base.uniontypes"]
        @test "Base.JuliaSyntax" in site_keys(non_public_accesses(Corset))
    end

    @testset "abstract-local: a local variable that infers no concrete type" begin
        @test site_keys(abstract_locals(repository, inferred)) == ["fixture.jl abstract_local"]
        @test isempty(abstract_locals(Repository(mktempdir()), inferred))
        @test occursin(r"^local `holder`::Vector.*Any", only(abstract_locals(repository, inferred)).detail)
        twins = [Site("k", "f", 3, "local `a`::Any"), Site("k", "f", 3, "local `b`::Any"), Site("k", "f", 3, "local `a`::Integer"), Site("k", "f", 4, "local `c`::Any")]
        @test [site.detail for site in Corset.one_per_line(twins)] == ["local `a`::Any; local `a`::Integer; local `b`::Any", "local `c`::Any"]
        @test [site.detail for site in Corset.one_per_line(reverse(twins))] == ["local `c`::Any", "local `a`::Any; local `a`::Integer; local `b`::Any"]
    end

    @testset "bang: a function that always returns nothing has a name ending in !" begin
        @test site_keys(unmarked_effects(repository, inferred)) == ["fixture.jl announce"]
    end

    @testset "impure, unstable and overspecialized anonymous functions" begin
        for (maker, argument) in ((:adder, 1), (:labeler, "a"), (:reader, [1]), (:kinded, Int))
            Base.invokelatest(Base.invokelatest(getfield(fixture, maker), argument), 2)
        end
        sites = Dict(site.key => site for site in impure_anonymous_functions(fixture))
        @test Set(keys(sites)) == Set(["fixture.jl boxed", "fixture.jl lineless", "fixture.jl reader"])
        @test sites["fixture.jl boxed"].detail == "holds a Core.Box: a captured variable is rebound"
        @test occursin("unverified", sites["fixture.jl lineless"].detail)
        @test sites["fixture.jl reader"].detail == "captures Vector{Int64}, not plain immutable data"
        overspecialized = only(Corset.overspecialized_anonymous_functions(fixture))
        @test overspecialized.key == "fixture.jl kinded"
        @test occursin("{Int64}, so it compiles once per value", overspecialized.detail)
        @test isempty(Corset.unstable_anonymous_functions(fixture))
        @testset "plain immutable data is a non-function bits value, a String or Symbol, or an immutable composite of them" begin
            @test all(Corset.plain_capture, (Int, Float32, Char, String, Symbol, Nothing, Tuple{Int, String}, @NamedTuple{name::String}, Union{Nothing, String}))
            @test !any(Corset.plain_capture, (Vector{Int}, Dict{Int, Int}, SubArray{Int, 1, Vector{Int}, Tuple{UnitRange{Int}}, true}, DataType, typeof(sin), Module, Real, Union{Int, Vector{Int}}))
            @test !Corset.plain_capture(TypeVar(:T))
        end
        @testset "each capture that is not plain data has one kind of fault" begin
            @test Corset.capture_kind.([Int, Vector{Int}, Module, Union{Int, Vector{Int}}, typeof(sin), Type{Int}, Real, Union{Int, Real}]) ==
                [:plain, :impure, :impure, :impure, :overspecialized, :overspecialized, :unstable, :unstable]
            @test Corset.capture_detail(:unstable, Real) == "captures Real, a type inference left abstract"
            @test Corset.instance_faults(Vector) == [:unstable => "built where the types of its captures are unknown"]
        end
        @testset "a closure built without line numbers sits at the function that creates it" begin
            fixture_lines = readlines(joinpath(root, "fixture.jl"))
            @test sites["fixture.jl lineless"].line == findfirst(startswith("@eval function lineless"), fixture_lines)
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
        @test struct_site(:Holder, struct_locations([path])) == Site("Holder", path, findfirst(==("struct Holder"), readlines(path)), "")
    end

    @testset "a struct is placed at its `struct` line, below its docstring" begin
        path = snippet_file("struct-line")
        lines = readlines(path)
        locations = struct_locations([path])
        @test locations == Dict(
            :Documented => (path, findfirst(startswith("struct Documented"), lines)),
            :Counter => (path, findfirst(endswith("struct Counter"), lines)),
            :Plain => (path, findfirst(startswith("struct Plain"), lines)),
            Symbol("Odd Name") => (path, findfirst(startswith("struct var\"Odd Name\""), lines)),
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
        @opt_sites "optimization analysis" dispatches target_modules = (fixture,) fixture.unstable(fixture.make_box())
        @test !isempty(dispatches)
        clean = Site[]
        @call_sites "error analysis" clean target_modules = (fixture,) fixture.reads_limit(1)
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
        @test site_keys(found_in(range_guards, "range-guard")) == ["guard", "edge", "finite"]
    end

    @testset "repeated-statement: a statement repeated in one block" begin
        sites = found_in(repeated_statements, "repeated-statement")
        @test length(sites) == 1
        @test startswith(only(sites).key, "twice: ")
        @test length(only(sites).key) > length("twice: ")
        @test only(sites).line == 3
    end

    @testset "return-type: Core.Compiler.return_type" begin
        @test site_lines(found_in(return_type_calls, "return-type")) == [1]
    end

    @testset "concrete-arg: an argument annotated with a concrete container it does not resize" begin
        @test site_lines(found_in(concrete_arguments, "concrete-arg")) == [1]
    end

    @testset "concrete-return: a result annotated with a concrete type, `Matrix{T}` included" begin
        sites = found_in((path, located) -> concrete_returns(path, located, Base), "concrete-return")
        @test site_keys(sites) == ["source.jl fixed", "source.jl squared"]
        logged = (:error, Regex("Fix: \\Q$CONCRETE_RETURN_FIX\\E"))
        @test (@test_logs logged offenders!(Repository(mktempdir()), "concrete-return", sites; fix = CONCRETE_RETURN_FIX)) == site_keys(sites)
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
        @test site_keys(found_in(missing_annotations, "annotation")) == ["source.jl untyped", "source.jl no_result"]
    end

    @testset "one-letter: one-letter variable names, with exemptions opt-in" begin
        path = snippet_file("one-letter")
        @test length(one_letter_sites(Repository(dirname(path)), path)) == 2
        @test length(one_letter_sites(Repository(dirname(path); one_letter_exempt = (:p,)), path)) == 1
    end

    @testset "fatou: findings of the real `fatou lint` (from mise.toml)" begin
        tree = write_tree(mktempdir(), ["src/source.jl" => SNIPPETS["fatou"]["source"], "clean/one.jl" => "one() = 1\n"])
        @test fatou_sites(Repository(tree), ("src",)) == [Site("src/source.jl unused-binding", joinpath(tree, "src", "source.jl"), 2, "")]
        @test isempty(fatou_sites(Repository(tree), ("clean",)))
        # fatou prints `error: failed to walk …`, no finding, for a missing directory.
        @test_throws ErrorException fatou_sites(Repository(tree), ("missing",))
        path = ENV["PATH"]
        try
            ENV["PATH"] = mktempdir()
            @test_throws ErrorException fatou_sites(Repository(tree), ("src",))
        finally
            ENV["PATH"] = path
        end
    end

    @testset "jscpd: findings of the real `jscpd` (from mise.toml)" begin
        copies = SNIPPETS["jscpd"]["source"]
        tree = write_tree(mktempdir(), ["copies.jl" => copies, "single.jl" => "one() = 1\n", "vendor/copies.jl" => copies])
        inner = Site("copies.jl copies.jl", joinpath(tree, "copies.jl"), 8, 14, "")
        vendored = Site("vendor/copies.jl copies.jl", joinpath(tree, "vendor", "copies.jl"), 1, 14, "")
        @test Set(jscpd_sites(Repository(tree), (".",))) == Set([inner, vendored])
        @test jscpd_sites(Repository(tree; skipped_directories = ("vendor",)), (".",)) == [inner]
        @test isempty(jscpd_sites(Repository(tree), ("nonexistent",)))
        @testset "a jscpd that writes no report, or none on PATH, is an error" begin
            path = ENV["PATH"]
            broken = write_tree(mktempdir(), ["jscpd" => "#!/bin/sh\nexit 1\n"])
            chmod(joinpath(broken, "jscpd"), 0o755)
            try
                ENV["PATH"] = "$broken:$path"
                @test_throws ErrorException jscpd_sites(Repository(tree), (".",))
                ENV["PATH"] = mktempdir()
                @test_throws ErrorException jscpd_sites(Repository(tree), (".",))
            finally
                ENV["PATH"] = path
            end
        end
    end

    @testset "misplaced-import: imports sit in the files that use them" begin
        snippets = SNIPPETS["misplaced-import"]
        tree = write_tree(mktempdir(), ["main.jl" => snippets["main"], "child.jl" => snippets["child"]])
        @test site_keys(misplaced_imports(Repository(tree), (".",))) == ["main.jl a", "main.jl c", "main.jl D"]
        place_imports!(Repository(tree), (".",))
        @test isempty(misplaced_imports(Repository(tree), (".",)))
        @testset "an import no file uses is deleted, one only an included file uses moves there" begin
            @test read(joinpath(tree, "main.jl"), String) == "module Main1\nusing A: b\ninclude(\"child.jl\")\nf() = b\nend\n"
        end
        @testset "a `using M: a, b` list splits across files; a name both files use stays put" begin
            @test read(joinpath(tree, "child.jl"), String) == "using A: a\nusing C: c\ng() = a + b + c\n"
        end
        @testset "an opted-out import and a bare `using` stay" begin
            kept_tree = write_tree(mktempdir(), ["kept.jl" => snippets["kept"]])
            place_imports!(Repository(kept_tree), (".",))
            @test read(joinpath(kept_tree, "kept.jl"), String) == snippets["kept"]
        end
    end

    @testset "misplaced-import: a name used only in a command interpolation counts as used" begin
        tree = write_tree(mktempdir(), ["cmd.jl" => "using A: a\nusing B: b\nusing C: c\nf() = `echo \$(a.x()) \$b \\\$c`\n"])
        @test site_keys(misplaced_imports(Repository(tree), (".",))) == ["cmd.jl c"]
        @testset "a `\$` inside single quotes is shell text, not an interpolation" begin
            quoted = write_tree(mktempdir(), ["cmd.jl" => "using A: a\nf() = `bash -c 'echo \"\$@\" \$a' x`\n"])
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
    result = placed(
        [
            "main.jl" => "using A: a\ninclude(\"child.jl\")\n",
            "child.jl" => "g() = a\n",
        ]
    )
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
        @test isempty(
            check(
                text,
                (path, located) -> concrete_returns(path, located, Main),
            )
        )
    end
    @testset "a positional argument still needs one" begin
        @test length(check("f(x)::Bool = true\n", missing_annotations)) == 1
    end
end

@testset "concrete-return: a package struct parameterized by a `where` variable is generic" begin
    scope = Module(:ReturnScope)
    Core.eval(
        scope, :(
            struct Wrapped{E}
                inner::E
            end
        )
    )
    Core.eval(
        scope, :(
            struct Set{E}
                inner::E
            end
        )
    )
    check(text::String) = (
        path = tempname() * ".jl";
        write(path, text);
        length(concrete_returns(path, located_source(path), scope))
    )
    @test check("(wrap(element::E)::Wrapped{E}) where {E} = Wrapped(element)\n") == 0
    @test check("(wrap(element::E)::Set{E}) where {E} = Set(element)\n") == 0
    @test check("(wrap(element::E)::Wrapped{E}) where {E <: Real} = Wrapped(element)\n") == 0
    @test check("function wrap(element::E)::Wrapped{E} where {E}\n    return Wrapped(element)\nend\n") == 0
    @test check("(wrap(elements::AbstractVector{E})::Wrapped{Vector{E}}) where {E} = Wrapped(collect(elements))\n") == 0
    @test check("(wrap(element::E)::Union{Nothing, Wrapped{E}}) where {E} = Wrapped(element)\n") == 0
    @test check("wrap(element::Float32)::Wrapped{Float32} = Wrapped(element)\n") == 1
    @test check("wrap(element::Float32)::Wrapped = Wrapped(element)\n") == 1
    @test check("(wrap(element::Float32)::Wrapped{E}) where {T} = Wrapped(element)\n") == 1
    @test check("(listed(element::E)::Vector{E}) where {E} = [element]\n") == 1
    # A macro-named function keys by the macro name alone, with no line-number node.
    path = tempname() * ".jl"
    write(path, "(@main)(args::AbstractVector)::Int = 0\n")
    @test only(concrete_returns(path, located_source(path), scope)).key == "$(basename(path)) @main"
end

@testset "a name used only inside a macro call counts as used" begin
    result = placed(
        [
            "main.jl" => "using A: a\ninclude(\"child.jl\")\n",
            "child.jl" => "@testset \"x\" begin\n    @test f(a(2))\nend\n",
        ]
    )
    @test result["child.jl"] == "using A: a\n@testset \"x\" begin\n    @test f(a(2))\nend\n"
end

@testset "import placement reads every include form and import shape" begin
    @testset "a moved import joins the imports the target file already has, at their indent" begin
        result = placed(["main.jl" => "using A: a\ninclude(\"child.jl\")\n", "child.jl" => "using C: c\ng() = a + c\n"])
        @test result["child.jl"] == "using C: c\nusing A: a\ng() = a + c\n"
        result = placed(["main.jl" => "module M\n    using A: a\n    include(\"child.jl\")\nend\n", "child.jl" => "    using C: c\n    g() = a + c\n"])
        @test result["child.jl"] == "    using C: c\n    using A: a\n    g() = a + c\n"
    end
    @testset "an import has nowhere to go in a module without imports" begin
        @test_throws ErrorException placed(["main.jl" => "using A: a\ninclude(\"child.jl\")\n", "child.jl" => "module Inner\ng() = a\nend\n"])
    end
    @testset "an unused import sharing its line with code is cut out of the line" begin
        @test placed(["main.jl" => "module M; using A: a; f() = 1; end\n"])["main.jl"] == "module M; ; f() = 1; end\n"
    end
    @testset "aliases, macros and string macros are names" begin
        @test placed(["main.jl" => "using A: a as b, @m\nf() = b\ng() = raw\"x\"\n"])["main.jl"] == "using A: a as b\nf() = b\ng() = raw\"x\"\n"
    end
    @testset "include paths: joinpath with @__DIR__ is followed, anything else blocks the move" begin
        files = ["main.jl" => "using A: a\ninclude(joinpath(@__DIR__, \"child.jl\"))\n", "child.jl" => "g() = a\n"]
        @test placed(files)["child.jl"] == "using A: a\ng() = a\n"
        for blocked in ("include(\"gone.jl\")", "include(name)", "include(string(\"child.jl\"))", "include(\"child.jl\", 1)")
            kept = "using A: a\n$blocked\n"
            @test placed(["main.jl" => kept, "child.jl" => "g() = a\n"])["main.jl"] == kept
        end
        cyclic = placed(["main.jl" => "using A: a\ninclude(\"child.jl\")\n", "child.jl" => "include(\"child.jl\")\ng() = a\n"])
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
        @test isempty(Corset.method_hidden_inputs(first(methods(Core.tuple))))
    end
    @testset "an anonymous function's own method is keyed by its file alone" begin
        @test Corset.method_key(only(methods(values -> values))) == "runtests.jl anonymous function"
    end
    @testset "abstract local types: unions, containers, tuples and Type" begin
        concrete = (Union{}, Union{Int, String}, Type{Int}, Vector{Int}, Dict{String, Int}, Tuple{Int, Float64}, Tuple{Vararg{Int}})
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
        @test Corset.testset_name(Meta.parse("@testset \"a b\" begin end")) === Symbol("a b")
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
        @test Corset.annotated_arguments(Expr(:parameters, Expr(:kw, :(k::Int), 1))) == [(:k, :Int)]
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

@testset "defined_methods finds methods added to another module's function" begin
    external = Module(:ExternalExtension)
    Base.eval(external, :(Base.length(::Type{Val{:corset_probe}})::Int = 1))
    defined = Corset.defined_methods(external)
    @test any(method -> method.name === :length && method.module === external, defined)
end

@testset "closure reflection follows nested closures and macro-made code" begin
    closure_chain = Module(:ClosureChain)
    Base.include(closure_chain, joinpath(FIXTURES, "closure_module.txt"))
    defined = Corset.defined_methods(closure_chain)
    namers = Corset.closure_namers(closure_chain, defined)
    @testset "a nested closure is defined by the function that holds the outermost one" begin
        @test Set(Corset.closure_definer(name, namers).name for name in keys(namers)) == Set([:nested, :recursive, :twice])
        @test length(Corset.live_closures(closure_chain, defined)) == length(namers)
    end
    @testset "code from a macro sits at the method's line, and a bare argument slot too" begin
        method = only(methods(closure_chain.uses_macro))
        code = Corset.lowered(method)
        @test any(index -> Corset.statement_line(code, method, index) == method.line, eachindex(code.code))
        @test Corset.slot_line(code, method, 2) == method.line
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
    idle()::Nothing = nothing
    struct Marker end
    struct Wrapped{M}
        marker::M
    end
    # `inner` must not be foldable: `outer` must keep an `:invoke` edge to it. A constant body
    # folds away when coverage is off (CI also runs that way), and the walk then finds no callee.
    @noinline inner(point::Marker)::Int = Int(time_ns() % 1) + 1
    @generated failing_generator(point::Marker)::Expr = error("the generator throws")
    outer(point::Marker)::Int = inner(point) + 1
    function passing(thunk::F) where {F}
        try
            return thunk()
        catch exception
            rethrow(exception)
        end
    end
end

@testset "abstract locals and bang names read the signatures given" begin
    signatures = Type[
        Tuple{typeof(Probe.generic), Vector{Float32}},
        Tuple{typeof(Probe.off), Nothing},
        Tuple{typeof(Probe.off), Float32},
        Tuple{typeof(Probe.catches)},
        Tuple{typeof(Probe.__init__)},
        Tuple{typeof(Probe.each_part), typeof(identity), Int},
        Tuple{typeof(Probe.each_part), typeof(string), Int},
        Tuple{typeof(Probe.passing), typeof(Probe.idle)},
        Tuple{typeof(Probe.matches), Vector{String}},
        Tuple{Type{Probe.Buffer}, Vector{Float32}, Int},
    ]
    repository = Repository(@__DIR__)
    inferred = inferred_methods(Probe, signatures)
    @testset "a generic method or constructor is typed at the signatures given, and a catch variable is skipped" begin
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
        @test !any(contains("passing"), [site.key for site in unmarked_effects(repository, inferred)])
    end
    @testset "inferred_methods depends on its signatures alone, not on what ran before" begin
        signatures = Type[Tuple{typeof(Probe.generic), Vector{Float32}}]
        cold = inferred_methods(Probe, signatures)
        Probe.generic(Float64[1, 2])
        Probe.generic(Int32[1, 2])
        warm = inferred_methods(Probe, signatures)
        @test [item.method for item in cold] == [item.method for item in warm]
        @test [item.method.name for item in warm] == [:generic]
        @test [item.code.slottypes for item in cold] == [item.code.slottypes for item in warm]
    end
end

module Mutation
    include(joinpath(@__DIR__, "fixtures", "mutation_module.txt"))
end

@testset "unmarked-mutation reads escape analysis over the walked frames" begin
    vector = Vector{Int}
    seeds = Type[
        Tuple{typeof(Mutation.direct), vector}, Tuple{typeof(Mutation.aliased), vector},
        Tuple{typeof(Mutation.setprop), Mutation.Box}, Tuple{typeof(Mutation.viafield), Mutation.Box},
        Tuple{typeof(Mutation.outer), vector}, Tuple{typeof(Mutation.far_outer), vector},
        Tuple{typeof(Mutation.viaindex), Vector{vector}}, Tuple{typeof(Mutation.stashed), vector},
        Tuple{typeof(Mutation.rebound), Memory{Int}}, Tuple{typeof(Mutation.viahelper), Mutation.Box},
        Tuple{typeof(Mutation.fresh)}, Tuple{typeof(Mutation.readonly), vector},
        Tuple{typeof(Mutation.addup), Int, Int}, Tuple{typeof(Mutation.reads), vector},
        Tuple{typeof(Mutation.bangwrite!), vector}, Tuple{typeof(Mutation.countdown), vector, Int},
        Tuple{typeof(Mutation.opaquecall), Function, vector}, Tuple{typeof(Mutation.viaccall), vector},
        Tuple{typeof(Mutation.opaqueglobal), Function},
        Tuple{typeof(Mutation.describe), IOBuffer, Mutation.Box}, Tuple{typeof(Mutation.log_to), IOStream, Mutation.Box},
        Tuple{typeof(Mutation.render), IOBuffer, Mutation.Box}, Tuple{typeof(Mutation.render_into), IOBuffer, Mutation.Box},
        Tuple{typeof(Mutation.log_context), IOContext{IOStream}, Mutation.Box},
        Tuple{typeof(Mutation.buffer_context), IOContext{IOBuffer}, Mutation.Box},
        Tuple{typeof(length), Mutation.Box}, Tuple{typeof(iterate), Mutation.Box}, Tuple{typeof(show), IOBuffer, Mutation.Box},
        Tuple{typeof(Mutation.guarded), ReentrantLock}, Tuple{typeof(Mutation.zero_first), vector},
    ]
    sites = Corset.unmarked_mutations(Repository(@__DIR__), inferred_methods(Mutation, entry_frames(seeds, Mutation)))
    details = Dict(last(split(site.key)) => site.detail for site in sites)
    @testset "a write through an argument, an alias, a field, an element or a callee is reported" begin
        for name in ("direct", "aliased", "setprop", "viafield", "outer", "far_helper", "far_outer", "viaindex", "stashed")
            @test startswith(get(details, name, ""), "writes argument")
        end
        @test details["direct"] == "writes argument `v` but its name has no `!`"
        @test details["zero_first"] == "writes argument `values` but its name has no `!`"
    end
    @testset "an IOBuffer and a lock are Julia objects; a file handle writes outside Julia" begin
        @test details["describe"] == "writes argument `io` but its name has no `!`"
        @test details["guarded"] == "writes argument `gate` but its name has no `!`"
        @test !haskey(details, "log_to")
        @test !Corset.writable(IOStream) && !Corset.writable(Base.PipeEndpoint) && !Corset.writable(Base.DevNull)
        @test Corset.writable(IOBuffer) && Corset.writable(Base.BufferStream) && Corset.writable(Base.LibuvStream)
        @test Corset.writable(IO) && Corset.writable(IOContext{IOBuffer}) && Corset.writable(ReentrantLock)
        @test !Corset.writable(IOContext{IOStream}) && Corset.writable(IOContext)
    end
    @testset "a method declaring an abstract IO writes its caller's stream; a concrete in-memory declaration flags" begin
        @test !haskey(details, "render") && !haskey(details, "render_into") && !haskey(details, "log_context")
        @test details["buffer_context"] == "writes argument `io` but its name has no `!`"
    end
    @testset "a writing method added to another module's non-`!` function breaks its contract" begin
        @test details["length"] == "adds a writing method to `Base.length`, which callers expect not to write: it writes argument `box`"
        @test details["iterate"] == "adds a writing method to `Base.iterate`, which callers expect not to write: it writes argument `box`"
        @test !haskey(details, "show")
        render = only(Corset.typed_frames(Tuple{typeof(Mutation.render), IOBuffer, Mutation.Box}))
        @test Corset.argument_writes(render, Dict{Core.MethodInstance, Corset.Inferred}(), (), Corset.CandidateSearch(Corset.Inferred[])).written == [2]
        @test Corset.declared_io(render.method, 2) && !Corset.declared_io(render.method, 3) && !Corset.declared_io(render.method, 9)
    end
    @testset "fresh memory, reads, a rebound local and a `!` function are not reported" begin
        for name in ("rebound", "viahelper", "fresh", "readonly", "addup", "reads", "bangwrite!", "countdown", "memwrite!", "fieldread", "opaqueglobal")
            @test !haskey(details, name)
        end
    end
    @testset "an argument passed to a runtime dispatch or a ccall may be written, never clean" begin
        @test details["opaquecall"] == "argument `x` reaches a runtime dispatch (`runtime-dispatch`) and may be written"
        @test details["viaccall"] == "argument `x` reaches a `ccall` and may be written"
    end
    @testset "Base.sort and Base.replace copy before they write" begin
        for signature in (Tuple{typeof(sort), vector}, Tuple{typeof(replace), vector, Pair{Int, Int}})
            writes = Corset.argument_writes(only(Corset.typed_frames(signature)), Dict{Core.MethodInstance, Corset.Inferred}(), (), Corset.CandidateSearch(Corset.Inferred[]))
            @test isempty(writes.written) && isempty(writes.dispatched) && isempty(writes.foreign)
        end
    end
end

module Dispatch
    include(joinpath(@__DIR__, "fixtures", "dispatch_module.txt"))
end

"""The sites of `sites` whose key names the function `name`."""
sites_named(sites::AbstractVector{Site}, name::AbstractString)::Vector{Site} = [site for site in sites if last(split(site.key)) == name]

@testset "runtime-dispatch and widened-return read the walked frames' optimized IR" begin
    untyped = Array{Any, 1}
    seeds = Type[
        Tuple{typeof(Dispatch.invoking_control), untyped}, Tuple{typeof(Dispatch.line_exempt), untyped},
        Tuple{typeof(Dispatch.exempt), untyped}, Tuple{typeof(Dispatch.widened_exempt), untyped},
        Tuple{typeof(Dispatch.opted_local), untyped}, Tuple{typeof(Dispatch.small_union), Bool},
        Tuple{typeof(Dispatch.splatted), untyped},
    ]
    repository = Repository(@__DIR__)
    inferred = inferred_methods(Dispatch, entry_frames(seeds, Dispatch))
    dispatches = runtime_dispatches(repository, inferred)
    widened = Dict(last(split(site.key)) => site.detail for site in widened_returns(repository, inferred))
    @testset "a noinline dynamic callee reached only through an :invoke edge is reported" begin
        control = only(sites_named(dispatches, "dispatching_control"))
        @test control.line == 2 && occursin("dispatches", control.detail) && occursin("+", control.detail)
        @test isempty(sites_named(runtime_dispatches(repository, inferred_methods(Dispatch, seeds)), "dispatching_control"))
        @test widened["invoking_control"] == "returns Any"
    end
    @testset "a statement's opt-out covers its line, a method's opt-out its whole body" begin
        @test [site.line for site in sites_named(dispatches, "line_exempt")] == [7, 8]
        @test [site.line for site in first(Corset.unopted(sites_named(dispatches, "line_exempt"), "runtime-dispatch"))] == [8]
        @test isempty(sites_named(dispatches, "exempt")) && !haskey(widened, "widened_exempt") && haskey(widened, "exempt")
    end
    @testset "a splat through Core._apply_iterate dispatches; a small concrete union compiles concretely" begin
        @test occursin("_apply_iterate", only(sites_named(dispatches, "splatted")).detail)
        @test !haskey(widened, "small_union") && isempty(sites_named(dispatches, "small_union"))
    end
    @testset "an abstract-local opt-out on a method's first line covers its locals" begin
        keys_ = [last(split(site.key)) for site in abstract_locals(repository, inferred)]
        @test "line_exempt" in keys_ && !("opted_local" in keys_)
    end
    @testset "compiled_concretely judges a returned tuple member by member" begin
        @test compiled_concretely(Tuple{Int, Union{Float32, Float16}})
        @test compiled_concretely(Tuple{Int, Tuple{Float32, Union{Nothing, Int}}})
        @test compiled_concretely(Union{}) && compiled_concretely(Type{Int})
        @test !compiled_concretely(Type{T} where {T})
        @test !compiled_concretely(Tuple{Int, Number})
        @test !compiled_concretely(Tuple{Int, Union{Int8, Int16, Int32, Int64, Int128}})
        @test !compiled_concretely(Tuple{Int, AbstractVector{Float32}})
        @test !compiled_concretely(Tuple{Vararg{Int}})
    end
end

module Candidates
    include(joinpath(@__DIR__, "fixtures", "candidates_module.txt"))
end

"""The seeds of the `Candidates` fixture: each caller over an untyped vector of shapes and a counter."""
candidate_seeds()::Vector{Type} = Type[
    Tuple{typeof(caller), Array{Any, 1}, Candidates.Counter}
        for caller in (Candidates.inspect, Candidates.record, Candidates.spread, Candidates.forward, Candidates.breaks, Candidates.echo, Candidates.splatted)
]

"""The frame of `caller` among `inferred`, and its one runtime-dispatch statement."""
function dispatch_statement(inferred::AbstractVector{Corset.Inferred}, caller::Function)::Tuple{Corset.Inferred, Expr}
    item = only([item for item in inferred if item.method.name === nameof(caller)])
    return item, only(filter(Base.Fix2(Corset.dispatches, item.ir), item.ir.stmts.stmt))
end

@testset "call_candidates lists a runtime dispatch's methods within its budget" begin
    inferred = inferred_methods(Candidates, entry_frames(candidate_seeds(), Candidates))
    search = Corset.CandidateSearch(inferred)
    item, statement = dispatch_statement(inferred, Candidates.inspect)
    @testset "four methods within the default budget are all inferred, each once" begin
        listed = Corset.call_candidates(statement, item.ir, search)
        @test listed.complete && Set(frame.method for frame in listed.frames) == Set(methods(Candidates.measure))
        known = length(search.frames)
        again = Corset.call_candidates(statement, item.ir, search)
        @test length(search.frames) == known && all(again.frames .=== listed.frames)
    end
    @testset "a budget cut, a zero budget and a splat list nothing and stay incomplete" begin
        for limit in (0, 3)
            cut = Corset.call_candidates(statement, item.ir, Corset.CandidateSearch(inferred; candidate_limit = limit))
            @test !cut.complete && isempty(cut.frames)
        end
        splat, splat_statement = dispatch_statement(inferred, Candidates.splatted)
        @test Corset.call_candidates(splat_statement, splat.ir, search) === Corset.NO_CANDIDATES
    end
    @testset "a candidate inference cannot type leaves the others and marks the list incomplete" begin
        broken, broken_statement = dispatch_statement(inferred, Candidates.breaks)
        partial = Corset.call_candidates(broken_statement, broken.ir, search)
        @test !partial.complete && length(partial.frames) == 3
    end
    @testset "a negative budget throws, and a candidate is named by module, file and line" begin
        @test_throws ArgumentError Corset.CandidateSearch(inferred; candidate_limit = -1)
        tally = only(methods(Candidates.tally, (Candidates.Circle, Candidates.Counter)))
        @test Corset.candidate_name(tally) == "$(Candidates).tally at candidates_module.txt:$(tally.line)"
    end
end

@testset "unmarked-mutation resolves a runtime dispatch through its candidates" begin
    inferred = inferred_methods(Candidates, entry_frames(candidate_seeds(), Candidates))
    repository = Repository(@__DIR__)
    "The details of `unmarked_mutations` at `limit`, by function name."
    details(limit::Integer)::Dict{String, String} = Dict(
        last(split(site.key)) => site.detail
            for site in Corset.unmarked_mutations(repository, inferred; search = Corset.CandidateSearch(inferred; candidate_limit = limit))
    )
    resolved = details(Corset.DEFAULT_CANDIDATE_LIMIT)
    may_write = "argument `counter` reaches a runtime dispatch (`runtime-dispatch`) and may be written"
    @testset "candidates that write nothing clear the site; a writing one makes it definite and is named" begin
        @test !haskey(resolved, "inspect")
        @test resolved["record"] == "writes argument `counter` but its name has no `!` (runtime-dispatch candidate `$(Corset.candidate_name(first(methods(Candidates.tally, (Candidates.Circle, Candidates.Counter)))))` writes it)"
        @test startswith(resolved["spread"], "writes argument `counter`") && occursin("gathered", resolved["spread"])
    end
    @testset "a budget cut keeps the conservative report" begin
        for limit in (0, 3)
            cut = details(limit)
            @test contains(cut["inspect"], may_write) && contains(cut["record"], may_write)
        end
    end
    @testset "an uninferable candidate, a candidate's own dispatch and a recursive candidate keep it too" begin
        for name in ("breaks", "forward", "echo")
            @test contains(resolved[name], may_write)
        end
    end
    @testset "a varargs candidate gathers the trailing operands into its last argument" begin
        gathered = only(methods(Candidates.gathered, (Candidates.Circle, Vararg{Candidates.Counter})))
        @test Corset.candidate_argument.((gathered,), 2:5) == [2, 3, 3, 3]
        @test Corset.candidate_argument(only(methods(Candidates.inspect)), 5) == 5
    end
end

module Floats
    include(joinpath(@__DIR__, "fixtures", "float_module.txt"))
end

@testset "float-widening: a float result wider than every float argument" begin
    untyped = Array{Any, 1}
    narrow = Float32
    seeds = Type[
        Tuple{typeof(Floats.scaled), narrow}, Tuple{typeof(Floats.halved), narrow}, Tuple{typeof(Floats.ratio), Int, Int, narrow},
        Tuple{typeof(Floats.floated), Int, Float16}, Tuple{typeof(Floats.global_scaled), narrow},
        Tuple{typeof(Floats.elementwise), Vector{narrow}}, Tuple{typeof(Floats.chained), narrow},
        Tuple{typeof(Floats.calls_widened), narrow}, Tuple{typeof(Floats.branchy), narrow, Bool}, Tuple{typeof(Floats.merged), narrow, Bool},
        Tuple{typeof(Floats.refined), narrow, Union{Nothing, narrow}}, Tuple{typeof(Floats.thrower), narrow},
        Tuple{typeof(Floats.wide), Float64}, Tuple{typeof(Floats.no_floats), Int},
        Tuple{typeof(Floats.grown), narrow, untyped}, Tuple{typeof(Floats.kept), narrow, untyped},
        Tuple{typeof(Floats.signed_only), narrow, Vector{Signed}},
    ]
    inferred = inferred_methods(Floats, entry_frames(seeds, Floats))
    repository = Repository(@__DIR__)
    "The `float_widenings` sites at `limit`, by function name."
    widenings(limit::Integer)::Dict{String, Site} = Dict(
        last(split(site.key)) => site
            for site in Corset.float_widenings(repository, inferred; search = Corset.CandidateSearch(inferred; candidate_limit = limit))
    )
    found = widenings(Corset.DEFAULT_CANDIDATE_LIMIT)
    @testset "a literal, a conversion, a float global, a callee and a returned literal widen, and name their source" begin
        # Julia 1.13 names the type `Base.Float64`; 1.14 names the binding `Core.Float64`.
        @test endswith(found["scaled"].detail, ".Float64` makes a Float64; the widest float argument is Float32")
        @test occursin("makes a Float64", found["global_scaled"].detail)
        @test occursin("the widest float argument is Float16", found["floated"].detail)
        @test found["calls_widened"].detail == "`widened` makes a Float64; the widest float argument is Float32"
        @test found["branchy"].detail == "`0.0` makes a Float64; the widest float argument is Float32"
        @test all(haskey.((found,), ["ratio", "elementwise", "widened"]))
    end
    @testset "a value computed from a widened one is not reported again" begin
        @test found["chained"].line == 9
    end
    @testset "narrow arithmetic, Float64 arguments, no float arguments and a throw are skipped" begin
        @test !any(haskey.((found,), ["halved", "wide", "no_floats", "refined", "thrower"]))
    end
    @testset "a dispatch: a wide candidate is definite, narrow ones clear it, a budget cut may widen" begin
        grow = only(methods(Floats.grow, (Float32,)))
        @test found["grown"].detail == "dispatches `$(GlobalRef(Floats, :grow))`; candidate `$(Corset.candidate_name(grow))` returns a float wider than Float32"
        @test !haskey(found, "kept")
        for limit in (0, 3)
            cut = widenings(limit)
            @test cut["kept"].detail == "dispatches `$(GlobalRef(Floats, :keep))` on a Float32 and may widen (`runtime-dispatch`)"
            @test endswith(cut["grown"].detail, "may widen (`runtime-dispatch`)")
        end
    end
    @testset "a dispatch whose operand types hold no float of the method's is skipped" begin
        @test !haskey(widenings(0), "signed_only")
        item, statement = dispatch_statement(inferred, Floats.signed_only)
        @test isnothing(Corset.dispatch_widening(statement, item.ir, Corset.float_budget(item), Corset.CandidateSearch(inferred; candidate_limit = 0)))
    end
    @testset "held_floats reads parameters, unions and type variables, to a depth limit" begin
        @test Corset.held_floats(Tuple{Int, Complex{Float16}}, 0) == [Float16]
        @test Set(Corset.held_floats(Union{Float32, Vector{Float64}}, 0)) == Set([Float32, Float64])
        @test isempty(Corset.held_floats(Vector{T} where {T}, 0)) && isempty(Corset.held_floats(Float32, 5))
        @test isempty(Corset.value_floats(Type{Float64}))
    end
    @testset "a φ merging a literal widens; a plain call is named by its callee" begin
        @test found["merged"].detail == "`0.0` makes a Float64; the widest float argument is Float32"
        @test Corset.callee_label(Expr(:call, GlobalRef(Base, :sqrt))) == "Base.sqrt"
        @test Corset.callee_label(GlobalRef(Base, :pi)) == "GlobalRef"
    end
end

@testset "entry_frames walks :invoke edges from the seeds and reads nothing the session ran" begin
    outer_call = Tuple{typeof(Probe.outer), Probe.Marker}
    inner_call = Tuple{typeof(Probe.inner), Probe.Marker}
    @testset "a noinline callee is followed, the seed is kept, and the answer does not depend on what ran" begin
        cold = collect(keys(entry_frames(Type[outer_call], Probe)))
        Probe.outer(Probe.Marker())
        @test Set(keys(entry_frames(Type[outer_call], Probe))) == Set(cold)
        @test outer_call in cold && inner_call in cold
    end
    @testset "entry_frames holds each signature's frames, empty where inference yields none" begin
        nothing_typed = Tuple{typeof(Probe.inner), String}
        frames = entry_frames(Type[outer_call, nothing_typed], Probe)
        @test Set(keys(frames)) == Set([outer_call, inner_call, nothing_typed])
        @test length(frames[outer_call]) == 1 && isempty(frames[nothing_typed])
    end
    @testset "inferred_methods reads the walk's frames and matches inferring the signatures anew" begin
        frames = entry_frames(Type[outer_call], Probe)
        walked = inferred_methods(Probe, frames)
        fresh = inferred_methods(Probe, collect(keys(frames)))
        @test Set(item.method for item in walked) == Set(item.method for item in fresh) == Set([only(methods(Probe.outer)), only(methods(Probe.inner))])
        @test all(item -> item.ir isa Base.Compiler.IRCode && !isempty(item.code.slottypes), walked)
    end
    @testset "a seed with no callee in the module is its own walk" begin
        @test collect(keys(entry_frames(Type[inner_call], Probe))) == Type[inner_call]
    end
    @testset "a method inference cannot type, a generator that throws, has no frame" begin
        @test isempty(Corset.typed_frames(Tuple{typeof(Probe.failing_generator), Probe.Marker}))
    end
    @testset "frame_callees keeps the callees naming the target and drops the others" begin
        ir = only(Corset.typed_frames(outer_call)).ir
        @test frame_callees(ir, Probe) == Type[inner_call]
        @test isempty(frame_callees(ir, Base))
    end
    @testset "mentions_module reads unions, where-types and nested parameters, to a depth limit" begin
        @test mentions_module(Probe.Marker, Probe, 0)
        @test mentions_module(Union{Probe.Marker, Int}, Probe, 0)
        @test mentions_module(Union{Int, Probe.Marker}, Probe, 0)
        @test mentions_module(Probe.Wrapped{Probe.Marker}, Probe, 0)
        @test mentions_module(Tuple{Vector{Probe.Marker}}, Probe, 0)
        @test mentions_module(Probe.Wrapped{M} where {M}, Probe, 0)
        @test !mentions_module(Vector{Int}, Probe, 0)
        @test !mentions_module(1, Probe, 0)
        @test !mentions_module(Union{Int, Float32}, Probe, 0)
        @test !mentions_module(Probe.Marker, Probe, 7)
    end
    @testset "invoked_instance and logging_call read each statement shape" begin
        instance = only(Base.specializations(only(methods(Probe.inner))))
        @test invoked_instance(instance) === instance
        @test invoked_instance(instance.cache) === instance
        @test invoked_instance("neither") === nothing
        @test logging_call(Expr(:call, GlobalRef(Base.CoreLogging, :handle_message)))
        @test logging_call(Expr(:call, Base.CoreLogging.handle_message))
        @test !logging_call(Expr(:call, :plain))
    end
end

@testset "module reflection compiles nothing per struct or closure of the checked package" begin
    Base.invokelatest(reflect_all, generated_module(20))
    # Specializing per binding compiled about 1.5 s here; the warm path compiles none.
    @test (@timed Base.invokelatest(reflect_all, generated_module(20))).compile_time < 0.25
end

include("entries.jl")
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
    # The annotation of a typed assignment is a use, not a definition.
    annotated = write_scan("@testset \"f\" begin\n x::GoneType = 1\n @test x == 1\nend\n")
    @test first(undefined_names(annotated; scope = @__MODULE__)) == ["line 1: `GoneType`"]
    # A qualified `Test.@testset` is scanned; a dotted import binds its last name.
    qualified = write_scan("Test.@testset \"f\" begin\n gone_name == 1\nend\n")
    @test first(undefined_names(qualified; scope = @__MODULE__)) == ["line 1: `gone_name`"]
    dotted = write_scan(
        "import Base.FastMath\nusing Base.Iterators\n@testset \"f\" begin\n @test FastMath isa Module\n @test Iterators isa Module\n @test take isa Function\nend\n",
    )
    @test first(undefined_names(dotted; scope = @__MODULE__)) == String[]
    # `@enum` binds its type and members, in a line or a `begin` block, with values and a base type.
    enums = write_scan(
        "@enum Color red blue = 2\n@enum Shade::UInt8 begin\n dark\n light = 3\nend\n@testset \"f\" begin\n @test red isa Color\n @test blue == blue\n @test dark isa Shade\n @test light isa Shade\n @test gone_member == 1\nend\n",
    )
    @test first(undefined_names(enums; scope = @__MODULE__)) == ["line 6: `gone_member`"]
    # A macro the scan has never seen may define any symbol among its arguments; test and logging macros define none.
    unknown = write_scan(
        "@never_seen_macro made_by_macro other = 1\n@testset \"f\" begin\n @test made_by_macro isa Any\n @test other == 1\n @test_throws ErrorException gone_name\n @info gone_logged\nend\n",
    )
    @test first(undefined_names(unknown; scope = @__MODULE__)) == ["line 2: `gone_logged`", "line 2: `gone_name`"]
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
        "using Corset\nimport Test\nusing NoSuchModuleAnywhere\nleft, (right, _) = 1, (2, 3)\ntyped_binding::Int = 1\nfunction no_methods end\n" *
            "function typed(x::T)::Int where {T}\n 1\nend\nstruct Wrapped{T} <: Any end\n" *
            "@testset \"f\" begin\n using Test: @test\n @test typed(left) + right + typed_binding == 4 && no_methods isa Function\n @test Wrapped{Int} isa Type\n" *
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

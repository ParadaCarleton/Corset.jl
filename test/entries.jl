# `Corset.Entries`: entry signatures from compiled specializations, concrete declarations, a test
# trace and a configured function. Each source is tested through its own API, with no rule run.

using Corset.Entries: Entries, entry_signatures

const ENTRY_DEMO = "module EntryDemo\ntwice(x) = 2x\nnamed(x::Symbol) = x\nend\n"

"""A fresh `EntryDemo` module, loaded from `ENTRY_DEMO` written under `root`."""
entry_demo(root::AbstractString)::Module =
    Base.include(Module(), joinpath(write_tree(root, ["EntryDemo.jl" => ENTRY_DEMO]), "EntryDemo.jl"))

"""A package `name` whose tests run `test_body`, under a fresh directory."""
traced_package(name::AbstractString, test_body::AbstractString)::String = write_tree(
    mktempdir(),
    [
        "Project.toml" => "name = \"$name\"\nuuid = \"aaaaaaaa-bbbb-cccc-dddd-000000000001\"\n",
        "src/$name.jl" => replace(ENTRY_DEMO, "EntryDemo" => name),
        "test/runtests.jl" => test_body,
    ],
)

@testset "Entries: compiled and declared signatures" begin
    demo = entry_demo(mktempdir())
    @test Entries.declared_signatures(demo) == Type[Tuple{typeof(demo.named), Symbol}]
    @test isempty(Entries.compiled_signatures(demo))
    Base.invokelatest(demo.twice, 1)
    @test Entries.compiled_signatures(demo) == Type[Tuple{typeof(demo.twice), Int}]
    @test Set(entry_signatures(demo)) == Set(Type[Tuple{typeof(demo.twice), Int}, Tuple{typeof(demo.named), Symbol}])
    @test entry_signatures(demo; sources = (:declared, :declared)) == Entries.declared_signatures(demo)
    @test isempty(entry_signatures(demo; sources = Symbol[]))
    @test_throws ArgumentError entry_signatures(demo; sources = (:nowhere,))
    @test_throws ArgumentError entry_signatures(demo; sources = (:tests,))
end

@testset "Entries: a trace keeps the module's concrete signatures and drops lines that fail to evaluate" begin
    demo = entry_demo(mktempdir())
    traced = Entries.trace_signatures(demo, joinpath(FIXTURES, "entries_trace.txt"))
    @test traced == Type[Tuple{typeof(demo.twice), Int}, Tuple{typeof(demo.twice), Float32}]
    scope = Entries.trace_scope(demo)
    @test isnothing(Entries.traced_type(scope, "precompile(Tuple{typeof(EntryDemo.twice), Main.TypeOnlyTheTestsDefine})"))
    @test_throws InterruptException Entries.traced_type(scope, "precompile(Tuple{throw(InterruptException())})")
    @test !Entries.defines(demo, nothing)
    @test !Entries.defines(demo, Tuple{typeof(demo.twice), Number})
end

@testset "Entries: the tests source traces a package's test run" begin
    package = traced_package("TracedDemo", "using TracedDemo\nTracedDemo.twice(Int8(1))\n")
    demo = Base.include(Module(), joinpath(package, "src", "TracedDemo.jl"))
    @test Tuple{typeof(demo.twice), Int8} in entry_signatures(demo; sources = (:tests,), root = package, unset = ("JULIA_LOAD_PATH",))
    failing = traced_package("FailingDemo", "error(\"a failing test\")\n")
    @test_throws ErrorException Entries.test_trace(failing, devnull)
end

@testset "Entries: a configured function returns the signatures" begin
    root = write_tree(mktempdir(), ["entries.jl" => "signatures() = Type[Tuple{typeof(identity), Symbol}]\nwrong() = [1]\n"])
    @test Entries.configured_signatures(joinpath(root, "entries.jl"), :signatures) == Type[Tuple{typeof(identity), Symbol}]
    @test_throws ErrorException Entries.configured_signatures(joinpath(root, "entries.jl"), :wrong)
end

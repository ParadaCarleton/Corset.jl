# `Corset.Membership`: a package's nested modules and loaded extensions are checked as the package.

module Nesting
    include(joinpath(@__DIR__, "fixtures", "nesting_module.txt"))
end

@testset "a nested module's structs, globals and frames belong to its package" begin
    package = Corset.Package(Nesting)
    @test Corset.belongs(Nesting.Nested, package) && !Corset.belongs(Main, package) && !Corset.belongs(Base, package)
    @test Set(module_structs(Nesting)) == Set([Nesting.Nested.Hidden, Nesting.Cell])
    @test "TALLY" in site_keys(hidden_inputs(Repository(@__DIR__), Nesting))
    vector = Vector{Int}
    seeds = Type[
        Tuple{typeof(Nesting.outer), vector}, Tuple{typeof(Nesting.reaches_nested), vector},
        Tuple{typeof(Nesting.lengths), Vector{Nesting.Cell}},
    ]
    frames = entry_frames(seeds, Nesting)
    @testset "the walk keeps an inlined helper, a nested callee and a method reached through Base, and drops Base's frames" begin
        @test issubset([:outer, :helper, :reaches_nested, :deep, :lengths, :length], [frame.method.name for frame in frames])
        @test all(Corset.belongs(frame.method.module, package) for frame in frames)
        @test allunique(frame.code.parent for frame in frames)
    end
    @testset "the rules report the inlined helper and the nested module's sites" begin
        details = Dict(last(split(site.key)) => site.detail for site in Corset.unmarked_mutations(Repository(@__DIR__), frames))
        @test details["helper"] == "writes argument `x` but its name has no `!`"
        @test !isempty(abstract_fields(Nesting.Nested.Hidden))
    end
end

"""A tree of two packages: `Hub`, with a submodule, and `Spoke`, which loads Hub's extension `HubSpokeExt`."""
extension_tree()::String = write_tree(
    mktempdir(),
    [
        "Hub/Project.toml" => """
            name = "Hub"
            uuid = "6a7c7e0e-2f43-4c5c-9b49-2a4f4f0e1a01"
            [weakdeps]
            Spoke = "6a7c7e0e-2f43-4c5c-9b49-2a4f4f0e1a02"
            [extensions]
            HubSpokeExt = "Spoke"
            """,
        "Hub/src/Hub.jl" => "module Hub\nmodule Inner\nstruct Deep end\nend\nf(x) = x\nend\n",
        "Hub/ext/HubSpokeExt.jl" => "module HubSpokeExt\nusing Hub: Hub\nusing Spoke: Spoke\nHub.f(::Spoke.S) = 1\nstruct ExtThing end\nend\n",
        "Spoke/Project.toml" => "name = \"Spoke\"\nuuid = \"6a7c7e0e-2f43-4c5c-9b49-2a4f4f0e1a02\"\n",
        "Spoke/src/Spoke.jl" => "module Spoke\nstruct S end\nend\n",
    ],
)

const EXTENSION_PROBE = """
using Corset: Corset
import Hub, Spoke
package = Corset.Package(Hub)
extension = Base.get_extension(Hub, :HubSpokeExt)
println(Corset.belongs(Hub.Inner, package), " ", Corset.belongs(extension, package), " ", Corset.belongs(Spoke, package))
println(join(sort(string.(nameof.(Corset.module_structs(Hub)))), ","))
println(join(sort(unique(string.(nameof.(getfield.(Corset.defined_methods(package), :module))))), ","))
"""

@testset "a loaded extension belongs to its parent package" begin
    command = `$(Base.julia_cmd()) --startup-file=no --project=$(Base.active_project()) -e $EXTENSION_PROBE`
    lines = readlines(addenv(command, "JULIA_LOAD_PATH" => "@:$(extension_tree()):@stdlib"))
    @test lines == ["true true false", "Deep,ExtThing", "Hub,HubSpokeExt,Inner"]
end

# The source rules of `syntax_hazards.jl`, each read from its snippet in `fixtures/snippets.toml`.

"""The lines of the sites `finder` finds in the snippet of `rule` that no `# lint: rule` comment opts out."""
function kept_lines(finder::Function, rule::AbstractString)::Vector{UnitRange{Int}}
    kept, _ = Corset.unopted(found_in(finder, rule), rule)
    return [site.line:site.last_line for site in kept]
end

@testset "a callee is named by its last plain name: `f`, `Base.f` and `f.(x)` call f" begin
    @test Corset.callee.([:(f(x)), :(Base.f(x)), :(f.(x)), :(handlers[1](x)), :(a.b), 1]) == [:f, :f, :f, Corset.NO_NAME, Corset.NO_NAME, Corset.NO_NAME]
    @test Corset.called_name(1) === Corset.NO_NAME
end

@testset "broad-catch: a catch block that rethrows nothing" begin
    @test kept_lines(Corset.broad_catches, "broad-catch") == [2:5, 9:12]
    @test length(found_in(Corset.broad_catches, "broad-catch")) == 3
    @test site_keys(found_in(Corset.broad_catches, "broad-catch"))[1:2] == ["source.jl swallowed", "source.jl mapped"]
    @test Corset.level(Corset.load_config(mktempdir()), Corset.BroadCatchRule()) === :deny
end

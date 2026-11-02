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

@testset "a literal is no path test, collection or name" begin
    @test !Corset.is_existence_predicate(1) && !Corset.is_name(1) && isempty(Corset.mentioned(1))
end

@testset "broad-catch: a catch block that rethrows nothing" begin
    @test kept_lines(Corset.broad_catches, "broad-catch") == [2:5, 9:12]
    @test length(found_in(Corset.broad_catches, "broad-catch")) == 3
    @test site_keys(found_in(Corset.broad_catches, "broad-catch"))[1:2] == ["source.jl swallowed", "source.jl mapped"]
    @test Corset.level(Corset.load_config(mktempdir()), Corset.BroadCatchRule()) === :deny
end

@testset "silent-existence-filter: a filter, mask or comprehension that drops missing paths" begin
    @test kept_lines(Corset.silent_existence_filters, "silent-existence-filter") == [1:1, 2:2, 3:3, 4:4, 6:6, 10:10, 11:11, 12:12]
    @test length(found_in(Corset.silent_existence_filters, "silent-existence-filter")) == 9
    @test first(site_keys(found_in(Corset.silent_existence_filters, "silent-existence-filter"))) == "source.jl present"
    @test Corset.level(Corset.load_config(mktempdir()), Corset.SilentExistenceFilterRule()) === :deny
end

@testset "quadratic-scan: a loop over a collection that scans it per element" begin
    sites = found_in(Corset.quadratic_scans, "quadratic-scan")
    @test kept_lines(Corset.quadratic_scans, "quadratic-scan") == [3:3, 8:8, 9:9, 10:10, 12:12, 16:16, 17:17, 18:18]
    @test length(sites) == 9
    @test last(sites).detail == "scans `items` once per element of `items`; group it once (a Dict, or sort and searchsorted)"
    @test sites[end - 1].detail == "scans `holder.items` once per element of `holder.items`; group it once (a Dict, or sort and searchsorted)"
    @test Corset.level(Corset.load_config(mktempdir()), Corset.QuadraticScanRule()) === :warn
end

@testset "non-atomic-write: several files written in turn, unstaged" begin
    @test kept_lines(Corset.non_atomic_writes, "non-atomic-write") == [2:2, 7:7, 8:8, 10:10, 17:17, 18:18, 34:34, 39:39]
    @test length(found_in(Corset.non_atomic_writes, "non-atomic-write")) == 9
    @test Corset.level(Corset.load_config(mktempdir()), Corset.NonAtomicWriteRule()) === :warn
end

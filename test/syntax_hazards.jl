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

@testset "a literal is no collection or name" begin
    @test !Corset.is_name(1) && isempty(Corset.mentioned(1))
end

@testset "broad-catch: a catch block that rethrows nothing" begin
    @test kept_lines(Corset.broad_catches, "broad-catch") == [2:5, 9:12]
    @test length(found_in(Corset.broad_catches, "broad-catch")) == 3
    @test site_keys(found_in(Corset.broad_catches, "broad-catch"))[1:2] == ["source.jl swallowed", "source.jl mapped"]
    @test Corset.level(Corset.load_config(mktempdir()), Corset.BroadCatchRule()) === :warn
end

@testset "quadratic-scan: a loop over a collection that scans it per element" begin
    sites = found_in(Corset.quadratic_scans, "quadratic-scan")
    @test kept_lines(Corset.quadratic_scans, "quadratic-scan") == [3:3, 8:8, 9:9, 10:10, 12:12, 16:16, 17:17, 18:18]
    @test length(sites) == 9
    @test last(sites).detail == "scans `items` once per element of `items`; group it once (a Dict, or sort and searchsorted)"
    @test sites[end - 1].detail == "scans `holder.items` once per element of `holder.items`; group it once (a Dict, or sort and searchsorted)"
    @test Corset.level(Corset.load_config(mktempdir()), Corset.QuadraticScanRule()) === :allow
end

@testset "quadratic-vcat: a fold that concatenates one piece at a time" begin
    @test kept_lines(Corset.quadratic_concatenations, "quadratic-vcat") == [1:1, 2:2, 3:3, 4:4, 5:5, 6:6, 8:8]
    sites = found_in(Corset.quadratic_concatenations, "quadratic-vcat")
    @test length(sites) == 8
    @test site_keys(sites)[[1, 7]] == ["source.jl seeded", "source.jl blocked"]
    @test Corset.level(Corset.load_config(mktempdir()), Corset.QuadraticVcatRule()) === :warn
    @test isempty(Corset.keyword_names(:(reduce(vcat, pieces))))
    @test Corset.keyword_names(:(reduce(vcat, pieces; options...))) == [Corset.NO_NAME]
end

@testset "non-atomic-write: several files written in turn, unstaged" begin
    @test kept_lines(Corset.non_atomic_writes, "non-atomic-write") == [2:2, 7:7, 8:8, 10:10, 17:17, 18:18, 34:34, 39:39]
    @test length(found_in(Corset.non_atomic_writes, "non-atomic-write")) == 9
    @test Corset.level(Corset.load_config(mktempdir()), Corset.NonAtomicWriteRule()) === :warn
end

@testset "banned-name: declared names with a banned word or suffix" begin
    function sites(text::String; words = ("key", "cell"), suffixes = ("_of",))::Vector{Site}
        root = write_tree(mktempdir(), ["a.jl" => text])
        return Corset.banned_name_sites(Repository(root; banned_words = words, banned_suffixes = suffixes), Source(Repository(root), joinpath(root, "a.jl")))
    end
    text = "owner_of(x) = x\nf(cell_key, Key) = haskey(cell_key, 1)\nstruct S\n    key::Int\n    ok::Int\nend\ng(x) = for cell in x\n    q = cell\nend\nh(x) = x\n"
    @test [site.line for site in sites(text)] == [1, 2, 2, 3, 7]
    @test isempty(sites(text; words = (), suffixes = ()))
    cells = Repository(mktempdir(); banned_words = ("cell",))
    @test Corset.is_banned(:Cell_Count, cells)
    @test !Corset.is_banned(:cellular, cells)
    @test Corset.load_config(mktempdir()).banned_words == ()
end

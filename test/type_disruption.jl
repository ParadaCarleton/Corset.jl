# `type-disruption`: its sub-checks `float-widening`, `float64` and `literal-array` keep their own names.

"""The `literal-array` lines of the Julia `text`."""
function literal_array_lines(text::AbstractString)::Vector{Int}
    tree = write_tree(mktempdir(), ["source.jl" => text])
    return [site.line for site in Corset.literal_array_sites(parsed(joinpath(tree, "source.jl")))]
end

@testset "literal-array: an array built from a literal container type" begin
    reported = """
    a(n::Int) = Vector{Float32}(undef, n)
    b(n::Int) = Matrix{Float32}(undef, n, n)
    c(n::Int) = Array{Float32}(undef, n, n, n)
    d(n::Int) = similar(Vector{Float32}, n)
    e(n::Int) = similar(Matrix, n, n)
    f(n::Int) = Base.Vector{Float32}(undef, n)
    """
    @test literal_array_lines(reported) == 1:6
    allowed = """
    a(x::AbstractVector, n::Int) = similar(x, Float32, n)
    b(::Type{A}, n::Int) where {A <: AbstractVector} = similar(A, n)
    c() = Float32[]
    d() = Vector{Float32}()
    e(x::AbstractVector) = Vector{Float32}(x)
    f(n::Int) = fill(0.0f0, n)
    """
    @test isempty(literal_array_lines(allowed))
end

@testset "type-disruption: sub-checks keep their names for levels, waivers and baselines" begin
    @test all(in(Corset.check_names()), ("float-widening", "float64", "literal-array"))
    @test !("type-disruption" in Corset.check_names())
    @test Corset.level(Corset.load_config(mktempdir()), Corset.Check("literal-array", :default, "")) === :warn
    @test Corset.level(Corset.load_config(mktempdir()), Corset.Check("float64", :pedantic, "")) === :allow
    @test_throws ArgumentError Corset.level(Corset.load_config(mktempdir()), Corset.TypeDisruptionRule())
    source = "module Demo\nmade(n::Int) = Vector{Float32}(undef, n)\nwaived(n::Int) = Vector{Float32}(undef, n) # lint: literal-array\nend\n"
    root = package_tree("name = \"Demo\"\n[preferences.Corset.levels]\nfloat64 = \"deny\"\nfloat-widening = \"allow\"\n", ["src/Demo.jl" => source * "wide(x::Float32)::Float32 = x * 2.0\n"])
    findings, skipped = Corset.run_rules(Corset.load_config(root), root)
    @test [(finding.rule, finding.level, finding.site.line) for finding in findings if finding.rule in ("literal-array", "float64", "float-widening")] == [("literal-array", :warn, 2), ("float64", :deny, 5)]
    @test "float-widening" ∉ skipped
    unwaived = package_tree("name = \"Demo\"\n", ["src/Demo.jl" => "module Demo\nmade(n::Int) = Vector{Float32}(undef, n)\nend\n"])
    findings, skipped = Corset.run_rules(Corset.load_config(unwaived), unwaived)
    @test "float-widening" in skipped
end

@testset "type-disruption: check is the union of the sub-check sites" begin
    root = package_tree("name = \"Demo\"\n", ["src/Demo.jl" => "module Demo\nmade(n::Int) = Vector{Float32}(undef, n)\nend\n"])
    context = Corset.Context(Corset.repository(Corset.load_config(root), root), ("src",), nothing)
    by_check = Corset.grouped_sites!(Corset.TypeDisruptionRule(), context)
    @test sort!(collect(keys(by_check))) == ["float-widening", "float64", "literal-array"]
    @test length(Corset.check(Corset.TypeDisruptionRule(), context)) == sum(length, values(by_check)) == 1
end

"""The text the `literal-array` fixer leaves of `text`, and the sites it repaired."""
function literal_arrayed(text::AbstractString)::Tuple{String, Vector{Int}}
    tree = write_tree(mktempdir(), ["source.jl" => text])
    sites = Corset.apply_plan!(Corset.literal_array_plan(Repository(tree), (".",)), "literal-array")
    return read(joinpath(tree, "source.jl"), String), [site.line for site in sites]
end

@testset "literal-array fixer: a parameter that sizes the array becomes its template" begin
    fixed(body::AbstractString) = first(literal_arrayed("f(x::AbstractVector{Float64}) = $body\n"))
    @test fixed("Vector{Float32}(undef, length(x))") == "f(x::AbstractVector{Float64}) = similar(x, Float32, length(x))\n"
    @test fixed("similar(Vector{Float32}, length(x))") == "f(x::AbstractVector{Float64}) = similar(x, Float32, length(x))\n"
    @test fixed("Array{Float32, 2}(undef, size(x))") == "f(x::AbstractVector{Float64}) = similar(x, Float32, size(x))\n"
    unchanged = (
        "Vector{Float32}(undef, 3)", "Vector{Float32}(undef, length(y))", "Vector(undef, length(x))", "Vector{Float32}(undef, length(x), 2)",
        "similar(x, Float32, length(x))",
    )
    for body in unchanged
        @test fixed(body) == "f(x::AbstractVector{Float64}) = $body\n"
    end
    for source in (
            "f(x::Vector{Float64}) = (x = other(); Vector{Float32}(undef, length(x)))\n", "f(x) = Vector{Float32}(undef, length(x))\n",
            "function f(x::Vector{Float64})\n    y::Vector{Float32} = Vector{Float32}(undef, length(x))\n    return y\nend\n",
        )
        @test first(literal_arrayed(source)) == source
    end
    waived = "f(x::Vector{Float64}) = Vector{Float32}(undef, length(x)) # lint: literal-array\n"
    @test first(literal_arrayed(waived)) == waived
    @test last(literal_arrayed("f(x::Vector{Float64}) = Vector{Float32}(undef, length(x))\n")) == [1]
end

@testset "literal-array fixer: --fix runs only while literal-array is on" begin
    source = "module Demo\nmade(x::Vector{Float64}) = Vector{Float32}(undef, length(x))\nend\n"
    for (levels, expected) in (("", "similar(x, Float32, length(x))"), ("literal-array = \"allow\"\n", "Vector{Float32}(undef, length(x))"))
        root = package_tree("name = \"Demo\"\n[preferences.Corset.levels]\n$levels", ["src/Demo.jl" => source])
        Corset.run_rules(Corset.load_config(root), root; fix = true)
        @test occursin(expected, read(joinpath(root, "src", "Demo.jl"), String))
    end
    @test Corset.fixable(Corset.TypeDisruptionRule())
end

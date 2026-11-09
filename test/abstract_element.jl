# `abstract-element`: a container built with an abstract element, key or value type.

module AbstractElementScope
    abstract type Shape end
    struct Circle <: Shape end
end

"""The texts `abstract-element` reports for `text`, resolving type names in `scope`."""
function abstract_texts(text::AbstractString, scope::Module = Base)::Vector{String}
    tree = write_tree(mktempdir(), ["source.jl" => text])
    return [SubString(site.detail, 2, findnext('`', site.detail, 2) - 1) for site in Corset.abstract_elements(parsed(joinpath(tree, "source.jl")), scope)]
end

@testset "abstract-element: a container with an abstract element, key or value type is reported" begin
    for (text, reported) in (
            "f(n) = Vector{Real}()" => ["Vector{Real}"],
            "f(n) = Vector{Real}(undef, n)" => ["Vector{Real}"],
            "f(m, n) = Matrix{Number}(undef, m, n)" => ["Matrix{Number}"],
            "f(n) = Array{AbstractFloat, 2}(undef, n, n)" => ["Array{AbstractFloat, 2}"],
            "f() = Dict{String, Any}()" => ["Dict{String, Any}"],
            "f() = Dict{Real, Int}()" => ["Dict{Real, Int}"],
            "f() = Set{Real}()" => ["Set{Real}"],
            "f() = Base.Vector{Integer}()" => ["Base.Vector{Integer}"],
            "f() = Real[]" => ["Real"],
            "f() = Any[1, \"a\"]" => ["Any"],
            "f(xs) = Real[x for x in xs]" => ["Real"],
            "f() = Number[1 2; 3 4]" => ["Number"],
            "f(x) = similar(x, Real)" => ["Real"],
            "f(x, n) = similar(x, Real, n)" => ["Real"],
            "f(n) = similar(Vector{Real}, n)" => ["Vector{Real}"],
            "f() = Vector{Vector}()" => ["Vector{Vector}"],
            "f() = Vector{Union{Real, Nothing}}()" => ["Vector{Union{Real, Nothing}}"],
        )
        @test abstract_texts(text) == reported
    end
    @test abstract_texts("f() = (Vector{Real}(), Set{Any}())") == ["Vector{Real}", "Set{Any}"]
end

@testset "abstract-element: a concrete element, an unresolved name and a use that is no construction pass" begin
    for text in (
            "f(n) = Vector{Float64}(undef, n)", "f() = Dict{String, Int}()", "f() = Set{Symbol}()", "f() = Float32[]", "f() = Vector{Union{Nothing, Int}}()",
            "f() = Vector{Complex{Float64}}()", "f() = Vector{Vector{Real}}()", "f() = Vector{Tuple{Int, Int}}()", "f(::Type{T}) where {T} = Vector{T}()",
            "f(x) = similar(x, Float32)", "f(x, n) = similar(x, n)", "f(x) = similar(x)", "f(x) = similar(x, 2, 3)", "f(xs) = xs[1]", "f(xs, i) = xs[i]",
            "f(x::Vector{Real}) = x", "g(xs) = convert(Vector{Real}, xs)", "f() = Vector{Missing}()", "f() = Type[Int, Float32]", "f() = Vector{Type}()", "f() = Dict(:a => 1)",
        )
        @test isempty(abstract_texts(text))
    end
end

@testset "abstract-element: a type name is resolved in the checked module" begin
    @test abstract_texts("f() = Vector{Shape}()", AbstractElementScope) == ["Vector{Shape}"]
    @test abstract_texts("f() = Vector{Circle}()", AbstractElementScope) == String[]
    @test abstract_texts("f() = Shape[]", AbstractElementScope) == ["Shape"]
    @test abstract_texts("f() = Vector{Shape}()") == String[]
    @test abstract_texts("f() = Vector{Real}()", AbstractElementScope) == ["Vector{Real}"]
end

@testset "abstract-element: a site takes a # lint: opt-out and the rule is pedantic" begin
    sites = found_in(source -> Corset.abstract_elements(source, Base), "abstract-element")
    @test length(sites) == 2
    @test Corset.level(Corset.load_config(mktempdir()), Corset.AbstractElementRule()) === :allow
    waived = "f() = Dict{String, Any}() # lint: abstract-element  JSON keeps any value\ng() = Vector{Real}()\n"
    tree = write_tree(mktempdir(), ["source.jl" => waived])
    source = parsed(joinpath(tree, "source.jl"))
    kept, _ = Corset.unopted(Corset.abstract_elements(source, Base), "abstract-element")
    @test [site.line for site in kept] == [2]
end

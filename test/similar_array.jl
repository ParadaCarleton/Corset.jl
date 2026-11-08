# `similar-array`: concrete array constructors are reported; an `undef` constructor sized by a parameter annotated as an array is fixed.

"""The `(form, template)` of every array construction in `text`, in source order."""
function constructions(text::AbstractString)::Vector{Tuple{Symbol, String}}
    tree = write_tree(mktempdir(), ["source.jl" => text])
    source = parsed(joinpath(tree, "source.jl"))
    return [(construction.form, construction.template) for construction in Corset.array_constructions(source.tree)]
end

"""The text the `similar-array` fixer leaves of `text`."""
function similarized(text::AbstractString)::String
    tree = write_tree(mktempdir(), ["source.jl" => text])
    Corset.apply_plan!(Corset.similar_array_plan(Repository(tree), (".",)), "similar-array")
    return read(joinpath(tree, "source.jl"), String)
end

"""The text the `nan-initializer` fixer leaves of `text`."""
function nan_initialized(text::AbstractString)::String
    tree = write_tree(mktempdir(), ["source.jl" => text])
    Corset.apply_plan!(Corset.nan_initializer_plan(Repository(tree), (".",)), "nan-initializer")
    return read(joinpath(tree, "source.jl"), String)
end

@testset "similar-array: every concrete constructor form is reported with its form, and an empty growable container is exempt" begin
    @test constructions("f(n) = Vector{Float32}(undef, n)\n") == [(:undef, "")]
    @test constructions("f(m, n) = Matrix{Float32}(undef, m, n)\n") == [(:undef, "")]
    @test constructions("f(dims) = Array{Float32}(undef, dims)\n") == [(:undef, "")]
    @test constructions("f(x) = Vector(x)\n") == [(:conversion, "")]
    @test constructions("f(x) = Vector{Float32}(x)\n") == [(:conversion, "")]
    @test constructions("f(n) = Matrix{Float32}(I, n, n)\n") == []
    @test constructions("f(n) = Vector{Union{Nothing, Int}}(nothing, n)\n") == []
    @test constructions("f(x) = Array(x)\n") == []
    @test constructions("f() = Array{Float32, 2}(undef, 3, 3)\n") == [(:undef, "")]
    @test constructions("f() = Float32[]\n") == []
    @test constructions("f() = Vector{Float32}()\n") == []
    @test constructions("f(x) = push!(Float32[], x)\n") == []
    @test constructions("f(x) = x[1]\ng(x) = zeros(Float32, 3)\n") == []
end

@testset "similar-array: an undef constructor sized by an annotated array parameter is fixed with explicit dimensions" begin
    @test constructions("f(x::AbstractVector) = Vector{Float32}(undef, length(x))\n") == [(:undef, "x")]
    @test similarized("f(x::AbstractVector{T}) where {T} = Vector{Float32}(undef, length(x))\n") == "f(x::AbstractVector{T}) where {T} = similar(x, Float32, length(x))\n"
    @test similarized("function f(x::Matrix{Float64})::Matrix{Float64}\n    return Matrix{Float64}(undef, size(x))\nend\n") == "function f(x::Matrix{Float64})::Matrix{Float64}\n    return similar(x, Float64, size(x))\nend\n"
    @test similarized("f(x::AbstractArray) = Array{E}(undef, size(x))\n") == "f(x::AbstractArray) = similar(x, E, size(x))\n"
    @test similarized("f(x::AbstractMatrix) = Vector{Float32}(undef, length(x))\n") == "f(x::AbstractMatrix) = similar(x, Float32, length(x))\n"
    @test similarized("function f(x::AbstractVector)\n    b = Vector{Float32}(undef, length(x))\n    b .= 1\n    return b\nend\n") == "function f(x::AbstractVector)\n    b = similar(x, Float32, length(x))\n    b .= 1\n    return b\nend\n"
    @test similarized("function f(x::AbstractVector, holder)\n    holder.buffer = Vector{Float32}(undef, length(x))\nend\n") == "function f(x::AbstractVector, holder)\n    holder.buffer = similar(x, Float32, length(x))\nend\n"
end

@testset "similar-array: a constructor without evidence that its template is an array is only reported" begin
    for text in (
            "f(x) = Vector{Float32}(undef, length(x))\n", "f(x::Tuple) = Vector{Float32}(undef, length(x))\n", "f(x::String) = Vector{UInt8}(undef, length(x))\n",
            "f(x::Dict) = Vector{Float32}(undef, length(x))\n", "f(x::AbstractVector, n) = Vector{Float32}(undef, n)\n", "g(x) = Vector(x)\n",
            "buffer = Vector{Float32}(undef, length(y))\n", "f(x::AbstractVector) = Vector(undef, length(x))\n", "f(x::AbstractVector) = Vector{Float32}(undef, length(x) + 1)\n",
            "function f(x::AbstractVector)\n    x = (1, 2, 3)\n    return Vector{Float64}(undef, length(x))\nend\n",
            "function f(x::AbstractVector)\n    x += 1\n    return Vector{Float64}(undef, length(x))\nend\n",
            "function f(x::AbstractVector)\n    (x, y) = (1, 2)\n    return Vector{Float64}(undef, length(x))\nend\n",
            "function f(x::AbstractVector, xs)\n    for x in xs\n    end\n    return Vector{Float64}(undef, length(x))\nend\n",
            "function f(x::AbstractVector)\n    return map(x -> Vector{Float64}(undef, length(x)), [1])\nend\n",
            "function f(x::AbstractVector)\n    return map([1]) do x\n        Vector{Float64}(undef, length(x))\n    end\nend\n",
            "function f(x::AbstractVector)\n    try\n        g()\n    catch x\n        return Vector{Float64}(undef, length(x))\n    end\nend\n",
            "function f(x::AbstractVector, host)\n    buffer = Vector{Float32}(undef, length(x))\n    copyto!(buffer, host)\n    return buffer\nend\n",
            "function f(x::AbstractVector, host)\n    buffer = Vector{Float32}(undef, length(x))\n    copy!(buffer, host)\n    return buffer\nend\n",
            "f(x::AbstractVector) = (b = Vector{Float32}(undef, length(x)); copyto!(b, x); b)\n",
            "function f(x::AbstractVector)\n    g = function (x)\n        return Vector{Float64}(undef, length(x))\n    end\n    return g\nend\n",
            "function f(x::AbstractVector, host)\n    b::Vector{Float32} = Vector{Float32}(undef, length(x))\n    copyto!(b, host)\n    return b\nend\n",
            "function f(x::AbstractVector, host)\n    b = Vector{Float32}(undef, length(x))\n    c = b\n    copyto!(c, host)\n    return b\nend\n",
            "function f(x::AbstractVector, host)\n    b = Vector{Float32}(undef, length(x))\n    c = b\n    d = c\n    copy!(d, host)\n    return b\nend\n",
            "function f(x::AbstractVector, host)\n    b = Vector{Float32}(undef, length(x))\n    c, d = b, b\n    copyto!(c, host)\n    return b\nend\n",
            "function f(x::AbstractVector, host)\n    b = Vector{Float32}(undef, length(x))\n    c = identity(b)\n    copyto!(c, host)\n    return b\nend\n",
            "function f(x::AbstractVector, host)\n    b = Vector{Float32}(undef, length(x))\n    fill_from(b, host)\n    return b\nend\n",
        )
        @test similarized(text) == text
    end
    @test constructions("f(x::Tuple) = Vector{Float32}(undef, length(x))\n") == [(:undef, "")]
end

@testset "similar-array: a site says why a construction has no replacement" begin
    for (text, expected) in (
            ("f(x::AbstractVector) = Vector{Float32}(undef, length(x))\n", "use `similar(x, Float32, length(x))`"), ("f(n) = Vector{Float32}(undef, n)\n", "known to be one"),
            ("f(x) = Vector(x)\n", "use `collect(x)`"), ("f(x) = Matrix{Float32}(x)\n", "use `collect(Float32, x)`"),
            ("f(s) = Vector{UInt8}(s)\n", "errors on non-ASCII"), ("f(x) = Vector(x)\n", "offers no fix"),
        )
        source = parsed(joinpath(write_tree(mktempdir(), ["source.jl" => text]), "source.jl"))
        @test occursin(expected, only(Corset.similar_array_sites([source])).detail)
    end
end

@testset "similar-array: the fixer is no --fix rule, and nan-initializer takes the template" begin
    @test !Corset.fixable(only(filter(rule -> Corset.rule_name(rule) == "similar-array", Corset.RULES)))
    body = "    x = zeros(Float32, length(y))\n    x .= 1\n    return x\nend\n"
    @test nan_initialized("function f(y::AbstractVector)\n$body") == "function f(y::AbstractVector)\n    x = fill!(similar(y, Float32, length(y)), NaN)\n    x .= 1\n    return x\nend\n"
end

@testset "similar-array: similar of a type is reported as a concrete constructor and takes an annotated array parameter as template" begin
    @test constructions("f(n) = similar(Vector{Float32}, n)\n") == [(:similar_type, "")]
    @test constructions("f(a, b) = fill!(similar(Matrix{Float32}, a, b), 0)\n") == [(:similar_type, "")]
    @test constructions("f(n) = similar(Array{Float32, 3}, n, n, n)\n") == [(:similar_type, "")]
    @test constructions("f(n) = similar(AbstractVector{Float32}, n)\n") == []
    @test constructions("f(::Type{A}, n) where {A <: AbstractVector} = similar(A, n)\n") == []
    @test constructions("f(x, n) = similar(x, Float32, n)\n") == []
    @test constructions("f(x, n) = similar(x, n)\n") == []
    @test constructions("f(x) = similar(x)\n") == []
    @test constructions("buffer = similar(Vector{Float32}, 3)\n") == [(:similar_type, "")]
    @test similarized("f(x::AbstractVector, n) = similar(Vector{Float32}, n)\n") == "f(x::AbstractVector, n) = similar(x, Float32, n)\n"
    @test similarized("f(x::AbstractMatrix, a, b) = fill!(similar(Matrix{Float32}, a, b), 0)\n") == "f(x::AbstractMatrix, a, b) = fill!(similar(x, Float32, a, b), 0)\n"
    @test similarized("f(n, x::AbstractArray) = similar(Array{Float32, 3}, n, n, n)\n") == "f(n, x::AbstractArray) = similar(x, Float32, n, n, n)\n"
    for text in ("f(n) = similar(Vector{Float32}, n)\n", "f(x, n) = similar(Vector{Float32}, n)\n", "f(x::AbstractVector, n) = similar(Vector, n)\n")
        @test similarized(text) == text
    end
    source = parsed(joinpath(write_tree(mktempdir(), ["source.jl" => "f(n) = similar(Vector{Float32}, n)\n"]), "source.jl"))
    @test occursin("thread an array type argument", only(Corset.similar_array_sites([source])).detail)
end

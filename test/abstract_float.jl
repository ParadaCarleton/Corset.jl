# `abstract-float`: an annotation or bound that names `AbstractFloat` takes `Real`, unless the method needs a float.

using Supposition: Supposition, Data, @check

"""The number of `abstract-float` sites in `text`."""
function float_site_count(text::AbstractString)::Int
    tree = write_tree(mktempdir(), ["source.jl" => text])
    return length(Corset.abstract_floats(parsed(joinpath(tree, "source.jl"))))
end

# Each syntax that annotates `AbstractFloat`, with how many sites it holds.
const FLOAT_FORMS = (
    "f(x::AbstractFloat) = x\n" => 1,
    "f(::AbstractFloat) = 1\n" => 1,
    "f(x::Real, y::AbstractFloat) = x\n" => 1,
    "f(; x::AbstractFloat = 1.0) = x\n" => 1,
    "f(xs::AbstractFloat...) = xs\n" => 1,
    "f(x::Real)::AbstractFloat = x\n" => 1,
    "f(x::T) where {T <: AbstractFloat} = x\n" => 1,
    "f(x::T) where T <: AbstractFloat = x\n" => 1,
    "function f(x::T) where {T <: AbstractFloat}\n    return x\nend\n" => 1,
    "f(x::AbstractVector{<:AbstractFloat}) = x\n" => 1,
    "f(x::AbstractVector{T}) where {T <: AbstractFloat} = x\n" => 1,
    "f(x::Union{Nothing, AbstractFloat}) = x\n" => 1,
    "f(x::Tuple{AbstractFloat, AbstractFloat}) = x\n" => 2,
    "f(x::Type{<:AbstractFloat}) = x\n" => 1,
    "f(x::Real) = x::AbstractFloat\n" => 1,
    "struct S{T <: AbstractFloat}\n    x::T\nend\n" => 1,
    "struct S\n    x::AbstractFloat\nend\n" => 1,
    "struct S{T <: AbstractFloat} <: AbstractVector{T}\n    x::T\nend\n" => 1,
    "const Alias = Vector{T} where {T <: AbstractFloat}\n" => 1,
)

# Text that mentions `AbstractFloat` outside an annotation or a bound, or needs no report.
const FLOAT_PASSES = (
    "f(x::Real) = x\n",
    "f(x::T) where {T <: Real} = x\n",
    "struct S <: AbstractFloat\n    x::Float32\nend\n",
    "f(::Type{T}) where {T} = T <: AbstractFloat\n",
    "f(x) = x isa AbstractFloat\n",
    "f(x) = if typeof(x) <: AbstractFloat\n    1\nelse\n    2\nend\n",
    "f(x::T) where {T >: AbstractFloat} = x\n",
    "const Names = (:AbstractFloat,)\n",
)

# Method bodies that need a float: each makes `AbstractFloat` the true requirement.
const FLOAT_BODIES = (
    "eps(x)", "nextfloat(x)", "prevfloat(x)", "floatmax(x)", "floatmin(x)", "significand(x)", "exponent(x)", "maxintfloat(x)", "issubnormal(x)",
    "reinterpret(UInt32, x)", "reinterpret(Int64, x)", "x + eps(typeof(x))",
)

@testset "abstract-float: every syntax that annotates AbstractFloat is reported" begin
    for (text, count) in FLOAT_FORMS
        @test float_site_count(text) == count
    end
    @test all(float_site_count(text) == 0 for text in FLOAT_PASSES)
    sites = found_in(Corset.abstract_floats, "abstract-float")
    @test [site.line for site in sites] == [1, 2, 3]
    @test all(occursin("write `Real`", site.detail) for site in sites)
end

@testset "abstract-float: a method that needs a float keeps AbstractFloat" begin
    for body in FLOAT_BODIES
        @test float_site_count("f(x::AbstractFloat) = $body\n") == 0
        @test float_site_count("function f(x::T)::T where {T <: AbstractFloat}\n    return $body\nend\n") == 0
    end
    @test float_site_count("f(x::AbstractFloat) = reinterpret(Float32, x)\n") == 1
    @test float_site_count("f(x::AbstractFloat) = eps(x)\ng(x::AbstractFloat) = x\n") == 1
    @test float_site_count("f(x::AbstractFloat) = (g(y::AbstractFloat) = eps(y); x)\n") == 0
    @test float_site_count("f(x::AbstractFloat) = (g(y::Real) = y; eps(x))\n") == 0
    @test float_site_count("struct S{T <: AbstractFloat}\n    x::T\nend\nf(x::Real) = eps(x)\n") == 1
end

@testset "abstract-float: the rule is pedantic and an opt-out comment silences it" begin
    @test Corset.level(Corset.load_config(mktempdir()), Corset.AbstractFloatRule()) === :allow
    path = joinpath(write_tree(mktempdir(), ["source.jl" => "f(x::AbstractFloat) = x # lint: abstract-float  dispatch splits floats from integers\n"]), "source.jl")
    kept, opted = Corset.unopted(Corset.abstract_floats(parsed(path)), "abstract-float")
    @test isempty(kept) && opted == 1
end

"""A definition around `annotation` with `body`, in one of the shapes `FLOAT_FORMS` holds."""
definition(shape::Int, annotation::String, body::String)::String =
    (
    "f(x::$annotation) = $body\n", "function f(x::T) where {T <: $annotation}\n    return $body\nend\n",
    "f(x)::$annotation = $body\n", "f(x::AbstractVector{<:$annotation}) = $body\n",
)[shape]

@testset "abstract-float: generated definitions keep the properties of the rule" begin
    mentions = Data.SampledFrom(1:4)
    names = Data.SampledFrom(("AbstractFloat", "Real", "Integer", "Number"))
    bodies = Data.SampledFrom(("x", "sqrt(x)", "x + 1", "zero(x)"))
    float_bodies = Data.SampledFrom(FLOAT_BODIES)
    report = @check max_examples = 300 db = false function float_properties(shape = mentions, name = names, body = bodies, needs = float_bodies)
        reported = float_site_count(definition(shape, name, body))
        mutated = float_site_count(definition(shape, "Real", body))
        exempt = float_site_count(definition(shape, name, needs))
        return reported == (name == "AbstractFloat" ? 1 : 0) && mutated == 0 && exempt == 0
    end
    @test Supposition.results(report).ispass
end

# The `abstract-float` fixer writes each reported `AbstractFloat` as `Real`.

"""The text the `abstract-float` fixer leaves of `text`."""
function realized(text::AbstractString)::String
    tree = write_tree(mktempdir(), ["source.jl" => text])
    Corset.apply_plan!(Corset.abstract_float_plan(Repository(tree), (".",)), "abstract-float")
    return read(joinpath(tree, "source.jl"), String)
end

@testset "abstract-float fixer: every reported mention becomes Real" begin
    for (text, _) in FLOAT_FORMS
        @test realized(text) == replace(text, "AbstractFloat" => "Real")
        @test float_site_count(realized(text)) == 0
    end
end

@testset "abstract-float fixer: text the rule leaves alone is left alone" begin
    for text in FLOAT_PASSES
        @test realized(text) == text
    end
    for body in FLOAT_BODIES
        @test realized("f(x::AbstractFloat) = $body\n") == "f(x::AbstractFloat) = $body\n"
    end
end

@testset "abstract-float fixer: a method with a sibling of its name keeps its signature" begin
    siblings = "f(x::AbstractFloat) = 1\nf(x::Integer) = 2\n"
    @test realized(siblings) == siblings
    @test realized("f(x::AbstractFloat) = 1\ng(x::AbstractFloat) = 2\n") == "f(x::Real) = 1\ng(x::Real) = 2\n"
    @test realized("struct S{T <: AbstractFloat}\n    x::T\nend\nf(x::AbstractFloat) = 1\nf(x::Integer) = 2\n") == "struct S{T <: Real}\n    x::T\nend\nf(x::AbstractFloat) = 1\nf(x::Integer) = 2\n"
end

@testset "abstract-float fixer: an opt-out comment pins its line" begin
    text = "f(x::AbstractFloat) = x # lint: abstract-float  dispatch splits floats from integers\ng(x::AbstractFloat) = x\n"
    @test realized(text) == replace(text, "g(x::AbstractFloat)" => "g(x::Real)")
end

@testset "abstract-float fixer: generated definitions are fixed once and idempotently" begin
    shapes = Data.SampledFrom(1:4)
    bodies = Data.SampledFrom(("x", "sqrt(x)", "x + 1", "zero(x)"))
    report = @check max_examples = 300 db = false function fixed_definition(shape = shapes, body = bodies)
        text = definition(shape, "AbstractFloat", body)
        fixed = realized(text)
        return fixed == definition(shape, "Real", body) && realized(fixed) == fixed
    end
    @test Supposition.results(report).ispass
end

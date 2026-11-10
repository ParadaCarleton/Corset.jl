# `unwritten-undef`: uninitialized arrays need a proof of a full write; written zeros, ones and fill arrays start as NaN.

"""The lines `unwritten-undef` reports in the one-file source `text`."""
unwritten_lines(text::AbstractString)::Vector{Int} = site_lines(Corset.unwritten_undef_sites([parsed(joinpath(write_tree(mktempdir(), ["source.jl" => text]), "source.jl"))]))

"""The `proof` of every written constant initializer in `text`, in source order."""
proofs(text::AbstractString)::Vector{Symbol} = [initializer.proof for initializer in Corset.nan_initializers(parsed(joinpath(write_tree(mktempdir(), ["source.jl" => text]), "source.jl")).tree)]

"""The text the `unwritten-undef` fixer leaves of `text`."""
function nanned(text::AbstractString)::String
    tree = write_tree(mktempdir(), ["source.jl" => text])
    Corset.apply_plan!(Corset.unwritten_undef_plan(Repository(tree), (".",)), "unwritten-undef")
    return read(joinpath(tree, "source.jl"), String)
end

"""A method that binds `constructor` to `x` on line 2, runs `body` and returns `x`."""
wrapped(body::AbstractString, constructor::AbstractString)::String = "function f(n, y)\n    x = $constructor\n$body\n    return x\nend\n"

const WHOLE_LOOP = "    for i in eachindex(x)\n        other = i\n        x[i] = other\n    end"
const GRID_LOOP = "    for j in axes(x, 2), i in axes(x, 1)\n        x[i, j] = i\n    end"

@testset "unwritten-undef: a full write before any read proves the array" begin
    for body in ("    x .= 1", "    fill!(x, 1)", "    copy!(x, y)", "    broadcast!(+, x, y, 1)", WHOLE_LOOP)
        @test all(isempty ∘ unwritten_lines ∘ Base.Fix1(wrapped, body), ("similar(y)", "Vector{Float32}(undef, n)", "similar(y, Float32, n)"))
        @test proofs(wrapped(body, "zeros(Float32, n)")) == [:initializer]
    end
    @test isempty(unwritten_lines(wrapped(GRID_LOOP, "Matrix{Float32}(undef, 2, n)")))
    @test proofs(wrapped(GRID_LOOP, "zeros(Float32, 2, n)")) == [:initializer]
    @test isempty(unwritten_lines("f(y) = Base.fill!(similar(y), NaN)\nsimilar(a::Box) = Box(similar(a.data))\ng(y) = quote\n    similar(\$y)\nend\n"))
end

@testset "unwritten-undef: a partial, conditional or reading write is reported" begin
    for body in (
            "    x[1] = 1", "    for i in eachindex(x)\n        if i > 1\n            x[i] = 1\n        end\n    end", "    for i in eachindex(x)\n        x[i] = x[i] + 1\n    end",
            "    for i in eachindex(x)\n        i > 2 && break\n        x[i] = 1\n    end", "    for i in 1:n\n        x[i] = 1\n    end", "    g!(x)",
            "    fill!(x, x)", "    x .= x .+ 1", "    for i in eachindex(x)\n        x[1] = 1\n    end", GRID_LOOP, "    Custom.fill!(x, 1)",
            "    for i in Custom.eachindex(x)\n        x[i] = 1\n    end", "    for i in Custom.axes(x, 1)\n        x[i] = 1\n    end",
            "    for i in eachindex(x)\n        i = 1\n        x[i] = 1\n    end", "    peek = () -> x[1]\n    fill!(x, peek())", "    map(1:2) do k\n        x[k]\n    end\n    x .= 1",
        )
        @test unwritten_lines(wrapped(body, "similar(y)")) == [2]
        @test proofs(wrapped(body, "zeros(n)")) == [:unproven]
    end
    @test unwritten_lines("f(y) = similar(y)\ng(y) = copy!(y, similar(y))\nh(y) = Custom.fill!(similar(y), 1)\nbuffer = Vector{Int}(undef, 3)\nbuffer .= 1\n") == [1, 2, 3, 4]
end

@testset "unwritten-undef: accumulators, unknown and NaN-less element types" begin
    @test all(isempty ∘ proofs, [wrapped(body, "zeros(n)") for body in ("    x[1] += 1", "    x .+= 1", "    sum(x)", "    for i in eachindex(x)\n        x[i] += i\n    end")])
    @test all(isempty ∘ proofs, [wrapped("    x .= 1", constructor) for constructor in ("fill(g(), n)", "SVector{3}(zeros(3))")])
    for constructor in ("zeros(N)", "zeros(T, n)", "zeros(elty, n)", "zeros(eltype(y), n)", "fill(zero(E), n)", "zeros(Float32, size(y))")
        @test proofs(wrapped(GRID_LOOP, constructor)) == [:unproven]
    end
    for constructor in ("zeros(Int, n)", "zeros(Cint, n)", "fill(0, n)", "fill(true, n)")
        @test proofs(wrapped("    x .= 1", constructor)) == [:nanless]
    end
    @test occursin("has no NaN", only(Corset.unwritten_undef_sites([parsed(joinpath(write_tree(mktempdir(), ["source.jl" => wrapped("    x .= 1", "zeros(Int, n)")]), "source.jl"))])).detail)
end

@testset "unwritten-undef: the fixer writes a NaN array of the same element type and size" begin
    for (constructor, nan) in ("zeros(Float32, n)" => "fill(Float32(NaN), n)", "zeros(n)" => "fill(NaN, n)", "Base.ones(Float64, (2, n))" => "fill(Float64(NaN), (2, n))", "fill(0.5f0, n)" => "fill(Float32(NaN), n)", "fill(0.5, n)" => "fill(NaN, n)", "fill(zero(Float16), n)" => "fill(Float16(NaN), n)")
        @test nanned(wrapped(WHOLE_LOOP, constructor)) == wrapped(WHOLE_LOOP, nan)
    end
    @test all(text -> nanned(text) == text, (wrapped("    x[1] = 1", "zeros(n)"), wrapped("    x .= 1", "zeros(Int, n)"), wrapped("    x .= 1", "zeros(T, n)")))
end

# `nan-initializer`: written zeros, ones and fill arrays start as NaN.

"""The `proof` of every written constant initializer in `text`, by callee name, in source order."""
function proofs(text::AbstractString)::Vector{Pair{String, Symbol}}
    tree = write_tree(mktempdir(), ["source.jl" => text])
    source = parsed(joinpath(tree, "source.jl"))
    return [initializer.name => initializer.proof for initializer in Corset.nan_initializers(source.tree)]
end

"""The text the `nan-initializer` fixer leaves of `text`."""
function nanned(text::AbstractString)::String
    tree = write_tree(mktempdir(), ["source.jl" => text])
    Corset.apply_plan!(Corset.nan_initializer_plan(Repository(tree), (".",)), "nan-initializer")
    return read(joinpath(tree, "source.jl"), String)
end

wrapped(body::AbstractString, constructor::AbstractString = "zeros(Float32, n)")::String = "function f(n)\n    x = $constructor\n$body\n    return x\nend\n"

@testset "nan-initializer: an array written in full before any read is an initializer" begin
    for body in (
            "    x .= 1", "    for i in eachindex(x)\n        x[i] = i\n    end",
            "    other = 2\n    for i in eachindex(x)\n        other += 1\n        x[i] = other\n    end",
        )
        @test proofs(wrapped(body)) == ["zeros" => :initializer]
    end
    @test proofs(wrapped("    for j in axes(x, 2), i in axes(x, 1)\n        x[i, j] = i\n    end", "zeros(Float32, 2, 3)")) == ["zeros" => :initializer]
    @test proofs(wrapped("    x .= 1", "ones(n)")) == ["ones" => :initializer]
    @test proofs(wrapped("    x .= 1", "fill(0.5f0, n)")) == ["fill" => :initializer]
    @test proofs(wrapped("    x .= 1", "fill(zero(Float32), n)")) == ["fill" => :initializer]
end

@testset "nan-initializer: a type the rule cannot classify, a dimension named like a type and a hidden rank are reported unproven" begin
    for constructor in ("zeros(N)", "zeros(Nx, Ny)", "zeros(T, n)", "zeros(elty, n)", "zeros(n, m)", "zeros(eltype(y), n)", "zeros(Union{Float64, Missing}, n)", "zeros(Rational{Int}, n)", "fill(zero(E), n)")
        @test only(last.(proofs(wrapped("    x .= 1", constructor)))) === :unproven
        @test nanned(wrapped("    x .= 1", constructor)) == wrapped("    x .= 1", constructor)
    end
    for constructor in ("zeros(Cint, n)", "zeros(BigInt, n)")
        @test only(last.(proofs(wrapped("    x .= 1", constructor)))) === :nanless
    end
    one_index = "    for i in axes(x, 1)\n        x[i] = 1.0\n    end"
    @test proofs(wrapped(one_index, "zeros(n, m)")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for j in axes(x, 2), i in axes(x, 1)\n        x[i, j] = 1.0\n    end", "zeros(n, m, 2)")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for j in axes(x, 2), i in axes(x, 1)\n        x[i, j] = 1.0\n    end", "zeros(size(y))")) == ["zeros" => :unproven]
    stencil = "    for i in eachindex(x)\n        x[i] = i\n        y[i] = x[min(i + 1, n)]\n    end"
    @test proofs(wrapped(stencil)) == ["zeros" => :unproven]
    @test proofs(wrapped("    for i in eachindex(x)\n        x[i] = i\n        x[i] = x[i] + x[max(i - 1, 1)]\n    end")) == ["zeros" => :unproven]
end

@testset "nan-initializer: a written array not provably an initializer is reported unproven" begin
    for body in (
            "    x[1] = 1", "    x[end] = 1\n    for i in eachindex(x)\n        x[i] = 1\n    end",
            "    for i in eachindex(x)\n        if i > 1\n            x[i] = 1\n        end\n    end",
            "    for i in eachindex(x)\n        x[i] = x[i] + 1\n    end", "    for i in eachindex(x)\n        i > 2 && break\n        x[i] = 1\n    end",
            "    for i in 1:n\n        x[i] = 1\n    end", "    fill!(x, 1)", "    x .= x .+ 1", "    g!(x)",
            "    for i in eachindex(x), j in 1:2\n        x[i] = j\n    end",
        )
        @test proofs(wrapped(body)) == ["zeros" => :unproven]
    end
    @test proofs(wrapped("    x[1] = 1")) == ["zeros" => :unproven]
    @test proofs(wrapped("    g!(x)")) == ["zeros" => :unproven]
    @test proofs(wrapped("    x .= x .+ 1")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for i in eachindex(x)\n        x[i] = x[i] + 1\n    end")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for i in eachindex(x)\n        i > 2 && break\n        x[i] = 1\n    end")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for i in 1:n\n        x[i] = 1\n    end")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for i in eachindex(x)\n        if i > 1\n            x[i] = 1\n        end\n    end")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for i in axes(x, 1)\n        x[i, 1] = 1\n    end", "zeros(Float32, 2, 3)")) == ["zeros" => :unproven]
    @test proofs(wrapped("    for i in eachindex(x)\n        x[1] = 1\n    end")) == ["zeros" => :unproven]
    @test proofs(wrapped("    x[1] = 1\n    x .= 2")) == ["zeros" => :unproven]
end

@testset "nan-initializer: accumulators, constants and escapes are silent" begin
    for body in ("    x[1] += 1", "    x .+= 1", "    x[1] = 1\n    x[2] += 1", "    for i in eachindex(x)\n        x[i] += i\n    end")
        @test proofs(wrapped(body)) == []
    end
    @test proofs("function f(n)\n    x = zeros(n)\n    return sum(x)\nend\n") == []
    @test proofs("function f(n)\n    x = zeros(n)\n    return x\nend\n") == []
    @test proofs("f(n) = zeros(n)\n") == []
    @test proofs("function f(n)\n    x = fill(g(), n)\n    x .= 1\n    return x\nend\n") == []
    @test proofs("function f(n)\n    x = SVector{3}(zeros(3))\n    return x\nend\n") == []
end

@testset "nan-initializer: an integer or Bool array has no NaN and is only reported" begin
    for constructor in ("zeros(Int, n)", "ones(Int32, n)", "zeros(Bool, n)", "fill(0, n)", "fill(true, n)", "zeros(UInt8, n)")
        @test only(last.(proofs(wrapped("    x .= 1", constructor)))) === :nanless
        @test nanned(wrapped("    x .= 1", constructor)) == wrapped("    x .= 1", constructor)
    end
    source = parsed(joinpath(write_tree(mktempdir(), ["source.jl" => wrapped("    x .= 1", "zeros(Int, n)")]), "source.jl"))
    @test occursin("has no NaN", only(Corset.nan_initializer_sites([source])).detail)
end

@testset "nan-initializer: the fixer writes a NaN array of the same element type and size" begin
    @test nanned(wrapped("    x .= 1")) == wrapped("    x .= 1", "fill(Float32(NaN), n)")
    @test nanned(wrapped("    x .= 1", "zeros(n)")) == wrapped("    x .= 1", "fill(NaN, n)")
    @test nanned(wrapped("    x .= 1", "ones(Float32, 2, n)")) == wrapped("    x .= 1", "fill(Float32(NaN), 2, n)")
    @test nanned(wrapped("    x .= 1", "Base.zeros(Float64, (2, n))")) == wrapped("    x .= 1", "fill(Float64(NaN), (2, n))")
    @test nanned(wrapped("    x .= 1", "fill(0.5f0, n)")) == wrapped("    x .= 1", "fill(Float32(NaN), n)")
    @test nanned(wrapped("    x .= 1", "fill(0.5, n)")) == wrapped("    x .= 1", "fill(NaN, n)")
    @test nanned(wrapped("    x .= 1", "fill(zero(Float16), n)")) == wrapped("    x .= 1", "fill(Float16(NaN), n)")
    loop = "    for i in eachindex(x)\n        x[i] = i\n    end"
    @test nanned(wrapped(loop)) == wrapped(loop, "fill(Float32(NaN), n)")
    unproven = wrapped("    x[1] = 1")
    @test nanned(unproven) == unproven
    accumulated = wrapped("    x[1] += 1")
    @test nanned(accumulated) == accumulated
    @test nanned(wrapped("    x .= 1", "fill(g(), n)")) == wrapped("    x .= 1", "fill(g(), n)")
end

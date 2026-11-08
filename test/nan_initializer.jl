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

@testset "nan-initializer: an array in scope that gives the dimensions becomes the template" begin
    argument = "function f(y::AbstractVector)\n    x = zeros(Float32, length(y))\n    x .= 1\n    return x\nend\n"
    @test nanned(argument) == "function f(y::AbstractVector)\n    x = fill!(similar(y, Float32, length(y)), NaN)\n    x .= 1\n    return x\nend\n"
    sized = "function f(y::Matrix)\n    x = zeros(size(y))\n    x .= 1\n    return x\nend\n"
    @test nanned(sized) == "function f(y::Matrix)\n    x = fill!(similar(y, Float64, size(y)), NaN)\n    x .= 1\n    return x\nend\n"
    local_template = "function f(z)\n    y = collect(z)\n    x = zeros(Float32, length(y))\n    x .= 1\n    return x\nend\n"
    @test nanned(local_template) == "function f(z)\n    y = collect(z)\n    x = fill!(similar(y, Float32, length(y)), NaN)\n    x .= 1\n    return x\nend\n"
    # A bare argument or a local of unknown kind may be a tuple or a string: no template.
    untyped = "function f(y)\n    x = zeros(Float32, length(y))\n    x .= 1\n    return x\nend\n"
    @test nanned(untyped) == "function f(y)\n    x = fill(Float32(NaN), length(y))\n    x .= 1\n    return x\nend\n"
    unknown_local = "function f(z)\n    y = g(z)\n    x = zeros(Float32, length(y))\n    x .= 1\n    return x\nend\n"
    @test nanned(unknown_local) == "function f(z)\n    y = g(z)\n    x = fill(Float32(NaN), length(y))\n    x .= 1\n    return x\nend\n"
    tree = write_tree(mktempdir(), ["source.jl" => argument])
    @test occursin("fill!(similar(y, Float32, length(y)), NaN)", only(Corset.nan_initializer_sites([parsed(joinpath(tree, "source.jl"))])).detail)
end

"""The `nan-initializer` fixer's replacement of `x = zeros(Float32, length(y))` placed in the `body` after the function's parameters, with `x .= 1` after it."""
function templated(parameters::AbstractString, before::AbstractString)::String
    return nanned("function f($parameters)\n$before    x = zeros(Float32, length(y))\n    x .= 1\n    return x\nend\n")
end

@testset "nan-initializer: only an array that reaches the construction is a template" begin
    plain = "fill(Float32(NaN), length(y))"
    # `copy` and `rand` build dictionaries, strings and scalars as well; a zero-dimensional `fill` has no length.
    @test occursin(plain, templated("d::Dict", "    y = copy(d)\n"))
    @test occursin(plain, templated("s::String", "    y = copy(s)\n"))
    @test occursin(plain, templated("", "    y = rand()\n"))
    @test occursin(plain, templated("", "    y = fill(0.5)\n"))
    @test occursin("similar(y, Float32", templated("", "    y = fill(0.5, 3)\n"))
    # A rebound parameter, a loop variable, and an assignment after the construction or in another branch do not reach it.
    @test occursin(plain, templated("y::AbstractVector, z", "    y = z\n"))
    @test occursin(plain, nanned("function f(y::AbstractVector, ys)\n    for y in ys\n        x = zeros(Float32, length(y))\n        x .= 1\n    end\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    y = collect(z)\n    for y in z\n        x = zeros(Float32, length(y))\n        x .= 1\n    end\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    x = zeros(Float32, length(y))\n    x .= 1\n    y = collect(z)\n    return x\nend\n"))
    # Every way to bind the name a second time anywhere in the function rules it out.
    body = "    x = zeros(Float32, length(y))\n    x .= 1\n"
    @test occursin(plain, nanned("function f(z)\n    y = collect(z)\n    let y = (1, 2)\n    $body    end\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    y = collect(z)\n    try\n        g()\n    catch y\n    $body    end\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    y = collect(z)\n    for i in 1:2\n    $body        y = (1, 2)\n    end\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    y = collect(z)\n    h = y -> y\n$body    return h\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    y = collect(z)\n    function g(y)\n        return y\n    end\n$body    return g\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    y, w = z\n$body    return w\nend\n"))
    @test occursin(plain, nanned("function f(z)\n    y = collect(z)\n    local y\n$body    return w\nend\n"))
    # A static-array builder is no template.
    @test occursin(plain, nanned("function f(z)\n    y = zeros(SVector{3})\n$body    return x\nend\n"))
    @test occursin("similar(y, Float32", nanned("function f(z)\n    y = zeros(3)\n$body    return x\nend\n"))
    @test occursin("similar(y, Float32", nanned("function f(z, c)\n    y = collect(z)\n    if c\n        x = zeros(Float32, length(y))\n        x .= 1\n    end\nend\n"))
end

@testset "nan-initializer: a local array in a top-level let is a template" begin
    @test occursin("similar(y, Float32", nanned("let z = 1\n    y = collect(z)\n    x = zeros(Float32, length(y))\n    x .= 1\nend\n"))
    @test occursin("fill(Float32(NaN), length(y))", nanned("let z = 1\n    x = zeros(Float32, length(y))\n    x .= 1\nend\n"))
end

@testset "nan-initializer: statements that do not bind the template are skipped" begin
    @test occursin("similar(y, Float32", templated("", "    y = collect(1:3)\n    other = 2\n"))
    @test occursin("fill(Float32(NaN), length(y))", templated("", "    other = 2\n"))
end

@testset "nan-initializer: a single non-array binding or an annotated signature" begin
    body = "    x = zeros(Float32, length(y))\n    x .= 1\n"
    @test occursin("fill(Float32(NaN), length(y))", nanned("function f(z)\n    y = z\n$body    return x\nend\n"))
    @test occursin("similar(y, Float32", nanned("function f(z)::Vector\n    y = collect(z)\n$body    return x\nend\n"))
    @test occursin("similar(y, Float32", nanned("function f(z::T) where {T}\n    y = collect(z)\n$body    return x\nend\n"))
end

@testset "nan-initializer: a binding inside another closure or a macro is no template" begin
    body = "    x = zeros(Float32, length(y))\n    x .= 1\n"
    plain = "fill(Float32(NaN), length(y))"
    @test occursin(plain, nanned("function f(n)\n    map(1:2) do i\n        y = zeros(n)\n        return y\n    end\n$body    return x\nend\n"))
    @test occursin(plain, nanned("function f(n)\n    h = () -> (y = zeros(n))\n$body    return x\nend\n"))
    @test occursin("similar(y, Float32", nanned("function f(n)\n    y = zeros(n)\n    map(1:2) do i\n    $body        return x\n    end\nend\n"))
    @test occursin(plain, nanned("function f(n)\n    y = zeros(n)\n    @variables y\n$body    return x\nend\n"))
end

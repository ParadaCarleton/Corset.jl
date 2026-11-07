# `constant-array`: calls of zeros, ones, fill, trues and falses that build an array no code writes.

"""The `usage` of every constant-array call in `text`, by callee name, in source order."""
function usages(text::AbstractString)::Vector{Pair{String, Symbol}}
    tree = write_tree(mktempdir(), ["source.jl" => text])
    return [call.name => call.usage for call in Corset.constant_array_calls(parsed(joinpath(tree, "source.jl")).tree)]
end

"""The text the `constant-array` fixer leaves of `text`; `unsafe` also repairs arrays that leave their function."""
function filled(text::AbstractString; unsafe::Bool = false)::String
    tree = write_tree(mktempdir(), ["source.jl" => text])
    Corset.apply_plan!(Corset.constant_array_plan(Repository(tree), (".",), unsafe), "constant-array")
    return read(joinpath(tree, "source.jl"), String)
end

@testset "constant-array: an array no code writes is a violation, a written one is silent" begin
    @test usages("f(n) = sum(zeros(n))\n") == ["zeros" => :safe]
    @test usages("f(n) = length(Base.ones(Float32, n))\n") == ["ones" => :safe]
    @test usages("function f(n)\n    x = zeros(n)\n    return sum(x) + x[1] + x[n - 1]\nend\n") == ["zeros" => :safe]
    @test usages("function f(n)\n    x = zeros(n)\n    for v in x\n        g(v)\n    end\nend\n") == ["zeros" => :safe]
    @testset "a written array has no FillArrays form" begin
        for written in (
                "x[1] = 2", "x[i] += 1", "x .= 1", "x .+= 1", "x[1:2] .= 0", "fill!(x, 1)", "mul!(x, a, b)", "LinearAlgebra.mul!(x, a, b)",
                "push!(x, 1)", "@. x = y + 1", "@views x[1:2] .= 0", "sort!(y, x)", "g!.(x)",
            )
            @test usages("function f(n)\n    x = zeros(n)\n    $written\n    return nothing\nend\n") == []
        end
        @test usages("f(n) = mul!(zeros(n), a, b)\n") == []
        @test usages("x::Vector{Float32} = zeros(Float32, 3)\n") == []
    end
    @testset "an array that leaves its function, or may alias, is an escape" begin
        for leaving in ("return x", "g(x)", "view(x, 1:2)", "x[1:2]", "x[idx()]", "@views x[1:2]", "y = x .+ 1", "x += 1", "x'", "Foo(x)")
            @test usages("function f(n)\n    x = zeros(n)\n    y = $leaving\n    return nothing\nend\n") == ["zeros" => :escape]
        end
        @test usages("f(n) = zeros(n)\n") == ["zeros" => :escape]
        @test usages("f(n) = Foo(buffer = zeros(n))\n") == ["zeros" => :escape]
        @test usages("BUFFER = zeros(3)\n") == ["zeros" => :escape]
        @test usages("function f(n)\n    x = zeros(n)\nend\n") == ["zeros" => :escape]
        @test usages("function f(n)\n    a = b = zeros(n)\n    return nothing\nend\n") == ["zeros" => :escape]
        @test usages("f(n) = [zeros(3) for _ in 1:n]\n") == ["zeros" => :escape]
    end
    @testset "a write inside a closure counts, a field or keyword of the same name does not" begin
        @test usages("function f(n)\n    x = zeros(n)\n    foreach(i -> (x[i] = 1), 1:n)\n    return nothing\nend\n") == []
        @test usages("function f(n)\n    x = zeros(n)\n    return sum(x) + a.x[1] + g(x = 2)\nend\n") == ["zeros" => :safe]
    end
    @testset "a definition of the function is no call" begin
        @test usages("zeros(n::Foo) = 1\nfunction fill(a::Foo, n)\n    return 1\nend\n") == []
        @test usages("f(zeros) = zeros + 1\ng(x) = fill + x\n") == []
    end
    @testset "fill: only an immutable value is certainly safe, an aliasing one is silent" begin
        @test usages("f(n) = sum(fill(0.5f0, n))\n") == ["fill" => :safe]
        @test usages("f(n) = sum(fill(zero(Float32), n))\n") == ["fill" => :safe]
        @test usages("f(n) = sum(fill(Float32(1), n))\n") == ["fill" => :safe]
        @test usages("f(n, v) = sum(fill(v, n))\n") == ["fill" => :escape]
        @test usages("f(n) = sum(fill(g(), n))\n") == ["fill" => :escape]
        for aliasing in ("[]", "Int[]", "Dict()", "[i for i in 1:2]", "Set{Int}()")
            @test usages("f(n) = sum(fill($aliasing, n))\n") == []
        end
        @test usages("f(n) = sum(fill([], n))\n") == []
        @test usages("f(n) = sum(fill(Vector{Int}(), n))\n") == []
    end
    @testset "trues and falses" begin
        @test usages("f(n) = count(falses(n)) + count(trues(n))\n") == ["falses" => :safe, "trues" => :safe]
        @test usages("function f(n)\n    mask = falses(n)\n    mask[1] = true\n    return mask\nend\n") == []
    end
end

@testset "constant-array: the fixer writes FillArrays constructors and imports them" begin
    @test filled("f(n) = sum(zeros(Float32, n))\n") == "using FillArrays: Zeros\n\nf(n) = sum(Zeros(Float32, n))\n"
    @test filled("using A: a\nf(n) = sum(Base.ones(n)) + sum(fill(1, 2, 3)) + count(trues(n)) + count(falses(n))\n") ==
        "using A: a\nusing FillArrays: Falses, Fill, Ones, Trues\nf(n) = sum(Ones(n)) + sum(Fill(1, 2, 3)) + count(Trues(n)) + count(Falses(n))\n"
    @test filled("using FillArrays: Zeros\nf(n) = sum(zeros(n))\n") == "using FillArrays: Zeros\nf(n) = sum(Zeros(n))\n"
    @test filled("using FillArrays\nf(n) = sum(zeros(n))\n") == "using FillArrays\nf(n) = sum(Zeros(n))\n"
    @test filled("import FillArrays\nf(n) = sum(zeros(n))\n") == "import FillArrays\nusing FillArrays: Zeros\nf(n) = sum(Zeros(n))\n"
    @test filled("module M\n    using A: a\n    f(n) = sum(zeros(n))\nend\n") == "module M\n    using A: a\n    using FillArrays: Zeros\n    f(n) = sum(Zeros(n))\nend\n"
    @testset "the fixer never turns a written array into a Fill" begin
        written = "function f(n)\n    x = zeros(n)\n    x[1] = 1\n    return x\nend\n"
        @test filled(written; unsafe = true) == written
        escaping = "f(n) = Foo(zeros(n))\n"
        @test filled(escaping) == escaping
        @test filled(escaping; unsafe = true) == "using FillArrays: Zeros\n\nf(n) = Foo(Zeros(n))\n"
        aliased = "f(n) = sum(fill([], n))\n"
        @test filled(aliased; unsafe = true) == aliased
    end
    @testset "a call a `# lint: constant-array` comment opts out stays, with no import" begin
        kept = "f(n) = sum(zeros(n)) # lint: constant-array  summed once\n"
        @test filled(kept) == kept
    end
    @testset "the fixed text parses and is no longer a violation" begin
        text = filled("f(n) = sum(zeros(n)) + sum(ones(n))\n")
        @test isempty(usages(text))
        @test Meta.parseall(text) isa Expr
    end
    @test Corset.level(Corset.load_config(mktempdir()), Corset.ConstantArrayRule()) === :allow
    @test Corset.fixable(Corset.ConstantArrayRule())
end

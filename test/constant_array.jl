# `constant-array`: calls of zeros, ones, fill, trues and falses that build an array no code writes.

"""The `usage` of every constant-array call in `text`, by callee name, in source order."""
function usages(text::AbstractString)::Vector{Pair{String, Symbol}}
    tree = write_tree(mktempdir(), ["source.jl" => text])
    source = parsed(joinpath(tree, "source.jl"))
    return [call.name => call.usage for call in Corset.constant_array_calls(source.tree, Corset.written_in([source]))]
end

"""The text the `constant-array` fixer leaves of `text`."""
function filled(text::AbstractString)::String
    tree = write_tree(mktempdir(), ["source.jl" => text])
    Corset.apply_plan!(Corset.constant_array_plan(Repository(tree), (".",)), "constant-array")
    return read(joinpath(tree, "source.jl"), String)
end

@testset "constant-array: an array no code writes is a violation, a written one is silent" begin
    @test usages("f(n) = sum(zeros(n))\n") == ["zeros" => :safe]
    @test usages("f(n) = length(Base.ones(Float32, n))\n") == ["ones" => :safe]
    @test usages("function f(n)\n    x = zeros(n)\n    return sum(x) + x[1] + x[end - 1]\nend\n") == ["zeros" => :safe]
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
    @testset "a rebinding of the name reads the array no more, a local declaration binds it" begin
        @test usages("function f(n)\n    x = zeros(n)\n    total = sum(x)\n    x = 2\n    return total\nend\n") == ["zeros" => :safe]
        @test usages("function f(n)\n    local x = zeros(n)\n    return sum(x)\nend\n") == ["zeros" => :safe]
    end
    @testset "a write inside a closure counts, a field or keyword of the same name does not" begin
        @test usages("function f(n)\n    x = zeros(n)\n    foreach(i -> (x[i] = 1), 1:n)\n    return nothing\nend\n") == []
        @test usages("function f(n)\n    x = zeros(n)\n    return sum(x) + a.x[1] + g(x = 2)\nend\n") == ["zeros" => :safe]
    end
    @testset "a definition of the function is no call" begin
        @test usages("zeros(n::Foo) = 1\nfunction fill(a::Foo, n)\n    return 1\nend\n") == []
        @test usages("ones(n::Foo)::Int = 1\nfunction trues(n::T)::Int where {T}\n    return 1\nend\n") == []
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
    @testset "a StaticArrays type builds a static array, which FillArrays has no form for" begin
        for static in ("zeros(SVector{3, Float32})", "ones(StaticArrays.SMatrix{2, 2})", "fill(0.0f0, SVector{3, Float32})", "zeros(MVector{3})", "fill(1, SArray)")
            @test usages("f() = sum($static)\n") == []
        end
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
        @test filled(written) == written
        escaping = "f(n) = Foo(zeros(n))\n"
        @test filled(escaping) == escaping
        aliased = "f(n) = sum(fill([], n))\n"
        @test filled(aliased) == aliased
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

"""The text of the `constant-array` fixer on the files `files` (name => text) of one tree, as name => text."""
function filled_tree(files::AbstractVector{<:Pair{String, String}})::Vector{Pair{String, String}}
    tree = write_tree(mktempdir(), files)
    Corset.apply_plan!(Corset.constant_array_plan(Repository(tree), (".",)), "constant-array")
    return [name => read(joinpath(tree, name), String) for (name, _) in files]
end

@testset "constant-array: reads that alias or slice an array are no safe reads" begin
    function inside(statement::String)::String
        return "function f(n, idx)\n    x = zeros(n)\n    $statement\n    return nothing\nend\n"
    end
    @testset "a destructuring assignment writes" begin
        @test usages(inside("x[1], x[2] = 1, 2")) == []
        @test usages(inside("x[1], x[2] = x[2], x[1]")) == []
        @test usages(inside("(x[1], y) = (1, 2)")) == []
        @test usages(inside("y, z = x, 1")) == ["zeros" => :escape]
    end
    @testset "a name or a range as an index may slice" begin
        for index in ("idx", "i", "idx + 1", "1:2", "[1]")
            @test usages(inside("y = x[$index]")) == ["zeros" => :escape]
        end
        @test usages(inside("y = x[2] + x[end] + x[end - 1]")) == ["zeros" => :safe]
    end
    @testset "a reader returns a scalar only without a count or a keyword" begin
        @test usages(inside("y = first(x) + last(x) + sum(x) + maximum(abs, x)")) == ["zeros" => :safe]
        @test usages(inside("y = mean(x)")) == ["zeros" => :safe]
        # `Zeros(n) isa Vector` is false and printing shows `Zeros(2)`: these see the array's type.
        for typed in ("y = x isa Vector", "println(x)", "print(x)", "show(x)", "y = string(x)", "y = typeof(x)")
            @test usages(inside(typed)) == ["zeros" => :escape]
        end
        @test usages(inside("y = mean(x; dims = 1)")) == ["zeros" => :escape]
        for array_reader in ("first(x, 2)", "last(x, 2)", "sum(x; dims = 1)", "sum(x, dims = 1)", "maximum(x; dims = 1)", "extrema(x; dims = 2)")
            @test usages(inside("y = $array_reader")) == ["zeros" => :escape]
        end
    end
    @testset "the broadcast macro writes through every assignment" begin
        @test usages(inside("@. x += 1")) == []
        @test usages(inside("@. x = 1")) == []
        @test usages(inside("@. y = x + 1")) == ["zeros" => :escape]
    end
end

@testset "constant-array: a call whose value may be the function's result escapes" begin
    @test usages("function f(c)\n    if c\n        x = zeros(3)\n    end\nend\n") == ["zeros" => :escape]
    @test usages("function f(c)\n    try\n        x = zeros(3)\n    catch\n    end\nend\n") == ["zeros" => :escape]
    @test usages("function f(c)\n    begin\n        x = zeros(3)\n    end\nend\n") == ["zeros" => :escape]
    @test usages("function f(c)\n    for i in 1:c\n        x = zeros(3)\n    end\n    return 1\nend\n") == ["zeros" => :safe]
    @test usages("function f(c)\n    x = zeros(3)\n    return sum(x)\nend\n") == ["zeros" => :safe]
end

@testset "constant-array: zero, one and oneunit give a number only from a type" begin
    @test usages("f(n, v) = sum(fill(zero(v), n))\n") == ["fill" => :escape]
    @test usages("f(n, v) = sum(fill(one(v), n))\n") == ["fill" => :escape]
    @test usages("f(n, v) = sum(fill(oneunit(v), n))\n") == ["fill" => :escape]
    @test usages("f(n) = sum(fill(zero(Float32), n))\n") == ["fill" => :safe]
    @test usages("f(n) = sum(fill(zero(T), n))\n") == ["fill" => :safe]
    @test usages("f(n, v) = sum(fill(zero(eltype(v)), n))\n") == ["fill" => :safe]
    @test usages("f(n, v) = sum(fill(one(typeof(v)), n))\n") == ["fill" => :safe]
    @test usages("f(n) = sum(fill(zero(Vector{Int}), n))\n") == ["fill" => :safe]
end

@testset "constant-array: the fixer imports FillArrays into the module of each call" begin
    @test filled("module Foo\nf(n) = sum(zeros(n))\nend\n") == "module Foo\nusing FillArrays: Zeros\nf(n) = sum(Zeros(n))\nend\n"
    @test filled("module A\nusing X: x\nf(n) = sum(zeros(n))\nend\nmodule B\nusing Y: y\nend\n") ==
        "module A\nusing X: x\nusing FillArrays: Zeros\nf(n) = sum(Zeros(n))\nend\nmodule B\nusing Y: y\nend\n"
    two = "module A\nf(n) = sum(zeros(n))\nend\nmodule B\ng(n) = sum(ones(n))\nend\n"
    @test filled(two) == "module A\nusing FillArrays: Zeros\nf(n) = sum(Zeros(n))\nend\nmodule B\nusing FillArrays: Ones\ng(n) = sum(Ones(n))\nend\n"
    @test filled("using FillArrays: Zeros\nmodule A\nf(n) = sum(zeros(n))\nend\n") ==
        "using FillArrays: Zeros\nmodule A\nusing FillArrays: Zeros\nf(n) = sum(Zeros(n))\nend\n"
    @test filled("module A\n    module B\n        f(n) = sum(zeros(n))\n    end\nend\n") ==
        "module A\n    module B\n        using FillArrays: Zeros\n        f(n) = sum(Zeros(n))\n    end\nend\n"
end

@testset "constant-array: the fixer lists FillArrays in the Project.toml above the file" begin
    project = "name = \"Demo\"\n\n[deps]\nA = \"11111111-1111-1111-1111-111111111111\"\n"
    source = "f(n) = sum(zeros(n))\n"
    listed = "using FillArrays: Zeros\n\nf(n) = sum(Zeros(n))\n"
    tree = Dict(filled_tree(["Project.toml" => project, "src/demo.jl" => source]))
    @test tree["Project.toml"] == "name = \"Demo\"\n\n[deps]\nFillArrays = \"1a297f60-69ca-5386-bcde-b61e274b549b\"\nA = \"11111111-1111-1111-1111-111111111111\"\n"
    @test tree["src/demo.jl"] == listed
    bare = Dict(filled_tree(["Project.toml" => "name = \"Demo\"\n", "src/demo.jl" => source]))
    @test bare["Project.toml"] == "name = \"Demo\"\n\n[deps]\nFillArrays = \"1a297f60-69ca-5386-bcde-b61e274b549b\"\n"
    present = "name = \"Demo\"\n\n[deps]\nFillArrays = \"1a297f60-69ca-5386-bcde-b61e274b549b\"\n"
    @test Dict(filled_tree(["Project.toml" => present, "src/demo.jl" => source]))["Project.toml"] == present
    @test Dict(filled_tree(["Project.toml" => "name = \"Demo\"", "src/demo.jl" => source]))["Project.toml"] ==
        "name = \"Demo\"\n\n[deps]\nFillArrays = \"1a297f60-69ca-5386-bcde-b61e274b549b\"\n"
end

@testset "constant-array: an array stored under a name some code writes through is written" begin
    sources_of(files) = Corset.directory_sources(Repository(write_tree(mktempdir(), files)), (".",))
    builder = "m(n) = (; sizes = zeros(Int, n), flags = fill(false, n))\n"
    @test length(Corset.constant_array_sites(sources_of(["a.jl" => builder]))) == 2
    field_write = Corset.constant_array_sites(sources_of(["a.jl" => builder, "b.jl" => "g(m) = (m.sizes[1] = 2)\n"]))
    @test length(field_write) == 1
    @test occursin("`fill`", only(field_write).detail)
    argument_write = Corset.constant_array_sites(sources_of(["a.jl" => builder, "b.jl" => "g(flags) = fill!(flags, true)\n"]))
    @test occursin("`zeros`", only(argument_write).detail)
    keyword = "make(n) = Holder(buffer = zeros(n))\n"
    @test length(Corset.constant_array_sites(sources_of(["a.jl" => keyword]))) == 1
    @test isempty(Corset.constant_array_sites(sources_of(["a.jl" => keyword, "b.jl" => "g(h) = (h.buffer .= 0)\n"])))
    local_name = "make(n) = begin\n    fresh = fill(false, n)\n    return Holder(fresh)\nend\n"
    @test length(Corset.constant_array_sites(sources_of(["a.jl" => local_name]))) == 1
    @test isempty(Corset.constant_array_sites(sources_of(["a.jl" => local_name, "b.jl" => "mark(job) = (job.fresh[1] = true)\n"])))
    kept = "make(n) = (; sizes = zeros(Int, n))\n"
    @test Dict(filled_tree(["a.jl" => kept, "b.jl" => "g(m) = (m.sizes[1] = 2)\n"]))["a.jl"] == kept
end

@testset "constant-array: an array passed to any call is reported and never rewritten" begin
    for passed in (
            "write!(x)", "g(; image = x)", "g(x; precision_slope = x)", "scribble(x)", "row_buffer(x)", "Foo(x)", "g.(x)",
            "setindex_all(x, 1)", "g(first(x, 2))",
        )
        text = "function f(n)\n    x = zeros(n)\n    $passed\n    return nothing\nend\n"
        @test filled(text) == text
        @test all(!=(:safe), last.(usages(text)))
    end
end

@testset "constant-array: a broadcast operator is no field access" begin
    @test usages("f(a, b) = a .+ b\ng(a, b) = (a .= b .* 2)\n") == []
    @test Corset.written_names(parsed(joinpath(write_tree(mktempdir(), ["s.jl" => "g(a, b) = (a .= b .* 2)\n"]), "s.jl")).tree) == [:variable => "a"]
end

@testset "constant-array: a field assignment, a local name, a CRLF project and a shebang" begin
    sources_of(files) = Corset.directory_sources(Repository(write_tree(mktempdir(), files)), (".",))
    field_target = "make(n) = begin\n    s = Holder()\n    s.buf = zeros(n)\n    return s\nend\n"
    @test length(Corset.constant_array_sites(sources_of(["a.jl" => field_target]))) == 1
    @test isempty(Corset.constant_array_sites(sources_of(["a.jl" => field_target, "b.jl" => "g(s) = (s.buf[1] = 2)\n"])))
    @test Dict(filled_tree(["a.jl" => field_target, "b.jl" => "g(s) = (s.buf[1] = 2)\n"]))["a.jl"] == field_target
    local_out = "make(n) = begin\n    out = zeros(n)\n    return Holder(out)\nend\n"
    @test length(Corset.constant_array_sites(sources_of(["a.jl" => local_out, "b.jl" => "g(out) = (out[1] = 2)\n"]))) == 1
    @test isempty(Corset.constant_array_sites(sources_of(["a.jl" => local_out, "b.jl" => "g(job) = (job.out[1] = 2)\n"])))
    source = "f(n) = sum(zeros(n))\n"
    for project in ("name = \"D\"\r\n\r\n[deps]\r\nA = \"11111111-1111-1111-1111-111111111111\"\r\n", "name = \"D\"\n\n[deps] # packages\nA = \"11111111-1111-1111-1111-111111111111\"\n")
        fixed = Dict(filled_tree(["Project.toml" => project, "src/demo.jl" => source]))
        @test TOML.parse(fixed["Project.toml"])["deps"]["FillArrays"] == "1a297f60-69ca-5386-bcde-b61e274b549b"
        @test startswith(fixed["src/demo.jl"], "using FillArrays: Zeros")
    end
    listed = "name = \"D\"\n\n[deps]\nFillArrays = \"1a297f60-69ca-5386-bcde-b61e274b549b\"\n"
    @test Dict(filled_tree(["Project.toml" => listed, "src/demo.jl" => source]))["Project.toml"] == listed
    @test Dict(filled_tree(["a.jl" => "#!/usr/bin/env julia\nf(n) = sum(zeros(n))\n"]))["a.jl"] == "#!/usr/bin/env julia\nusing FillArrays: Zeros\n\nf(n) = sum(Zeros(n))\n"
end

@testset "constant-array: a Project.toml the fixer cannot extend fails loud, before any file changes" begin
    project = "name = \"D\"\nnote = \"\"\"\n[deps]\n\"\"\"\n"
    tree = write_tree(mktempdir(), ["Project.toml" => project, "src/demo.jl" => "f(n) = sum(zeros(n))\n"])
    plan = Corset.constant_array_plan(Repository(tree), (".",))
    @test_throws ArgumentError Corset.apply_plan!(plan, "constant-array")
    @test read(joinpath(tree, "src/demo.jl"), String) == "f(n) = sum(zeros(n))\n"
end

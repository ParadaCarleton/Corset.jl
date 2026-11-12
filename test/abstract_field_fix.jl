# `abstract-field` fixer: a struct with abstract fields becomes a `@concrete struct` whose abstract fields read `x <: T`,
# unless the macro cannot express it or a later write could retype a field.

const CONCRETE_IMPORT = "using ConcreteStructs: @concrete\n\n"

"""The text the abstract-field fixer leaves of the files `files` (name => text), by name."""
function abstract_field_fixed(files::AbstractVector{<:Pair})::Dict{String, String}
    tree = write_tree(mktempdir(), files)
    Corset.unsafe_fix!(Corset.AbstractFieldRule(), Repository(tree), (".",))
    return Dict(name => read(joinpath(tree, name), String) for name in first.(files))
end

"""The text the abstract-field fixer leaves of the single file `text`."""
abstract_field_fixed(text::AbstractString)::String = abstract_field_fixed(["source.jl" => text])["source.jl"]

"""The `abstract_fields` of struct `name` after loading `text` as a module."""
function loaded_abstract_fields(text::AbstractString, name::Symbol)::Vector{Symbol}
    holder = Module(:Loaded)
    Base.include_string(holder, text)
    return abstract_fields(Base.unwrap_unionall(getglobal(holder, name)))
end

"""Whether the fixer leaves `text` as it is."""
unfixed(text::AbstractString)::Bool = abstract_field_fixed(text) == text

@testset "abstract-field: the fixer writes @concrete structs" begin
    @testset "an abstract field reads <: its old type, and the macro appends the parameter after the existing ones" begin
        @test abstract_field_fixed("struct S\n    x::AbstractVector{Int}\nend\n") == CONCRETE_IMPORT * "@concrete struct S\n    x <: AbstractVector{Int}\nend\n"
        @test abstract_field_fixed("struct S{E}\n    x::AbstractVector{E}\n    y::E\nend\n") == CONCRETE_IMPORT * "@concrete struct S{E}\n    x <: AbstractVector{E}\n    y::E\nend\n"
        @test abstract_field_fixed("struct S{E}\n    x::AbstractVector{E}\n    y::Real\nend\n") == CONCRETE_IMPORT * "@concrete struct S{E}\n    x::AbstractVector{E}\n    y <: Real\nend\n"
        @test abstract_field_fixed("struct S{E <: Real} <: Base.AbstractSet{E}\n    n::Integer\nend\n") == CONCRETE_IMPORT * "@concrete struct S{E <: Real} <: Base.AbstractSet{E}\n    n <: Integer\nend\n"
        @test abstract_field_fixed("mutable struct S\n    f::Function\n    n::Int\nend\n") == CONCRETE_IMPORT * "@concrete mutable struct S\n    f <: Function\n    n::Int\nend\n"
        @test abstract_field_fixed("\"\"\"A pair.\"\"\"\nstruct S\n    \"left\"\n    a::Real\n    b::AbstractString\n    c::Int\nend\n") ==
            CONCRETE_IMPORT * "\"\"\"A pair.\"\"\"\n@concrete struct S\n    \"left\"\n    a <: Real\n    b <: AbstractString\n    c::Int\nend\n"
    end

    @testset "the import goes into the module that holds the struct, once" begin
        @test abstract_field_fixed("module M\nstruct S\n    x::Real\nend\nstruct T\n    y::Real\nend\nend\n") ==
            "module M\nusing ConcreteStructs: @concrete\n@concrete struct S\n    x <: Real\nend\n@concrete struct T\n    y <: Real\nend\nend\n"
        imported = "using ConcreteStructs: @concrete\nstruct S\n    x::Real\nend\n"
        @test abstract_field_fixed(imported) == "using ConcreteStructs: @concrete\n@concrete struct S\n    x <: Real\nend\n"
        @test abstract_field_fixed("using ConcreteStructs\nstruct S\n    x::Real\nend\n") == "using ConcreteStructs\n@concrete struct S\n    x <: Real\nend\n"
    end

    @testset "the Project.toml lists ConcreteStructs" begin
        tree = write_tree(mktempdir(), ["Project.toml" => "name = \"P\"\n", "src/P.jl" => "struct S\n    x::Real\nend\n"])
        Corset.unsafe_fix!(Corset.AbstractFieldRule(), Repository(tree), ("src",))
        @test TOML.parsefile(joinpath(tree, "Project.toml"))["deps"]["ConcreteStructs"] == "2569d6c7-a4a2-43d3-a901-331e8e4be471"
    end

    @testset "abstract types the checked files declare count, the types they do not resolve do not" begin
        shapes = "abstract type Shape end\nabstract type Round <: Shape end\nstruct Circle <: Round\n    r::Float32\nend\n"
        @test abstract_field_fixed(shapes * "struct S\n    s::Shape\n    t::Round\n    u::Circle\nend\n") ==
            CONCRETE_IMPORT * shapes * "@concrete struct S\n    s <: Shape\n    t <: Round\n    u::Circle\nend\n"
        @test unfixed("struct S\n    x::Imported.AbstractThing\n    y::AbstractThing\nend\n")
        @test unfixed("abstract type Both end\nstruct Both\n    x::Int\nend\nstruct S\n    b::Both\nend\n")
        @test unfixed("struct S{Real}\n    a::Real\nend\n")
        @test unfixed("module A\nabstract type Shape end\nend\nmodule B\nusing Other: Shape\nstruct S\n    s::Shape\nend\nend\n")
        @test unfixed("module A\nabstract type Shape end\nend\nmodule B\nstruct S\n    s::Shape\nend\nend\n")
        @test unfixed("module A\nabstract type Shape end\nimport Other: Shape\nstruct S\n    s::Shape\nend\nend\n")
        @test abstract_field_fixed("module A\nabstract type Shape end\nstruct S\n    s::Shape\nend\nend\nmodule B\nstruct T\n    s::Real\nend\nend\n") ==
            "module A\nusing ConcreteStructs: @concrete\nabstract type Shape end\n@concrete struct S\n    s <: Shape\nend\nend\nmodule B\nusing ConcreteStructs: @concrete\n@concrete struct T\n    s <: Real\nend\nend\n"
    end

    @testset "Any, concrete containers and concrete types stay" begin
        @test unfixed("struct S\n    a::Any\n    b::Vector{Any}\n    c::Type\n    d::Int\n    e::Union{Nothing, Real}\nend\n")
    end

    @testset "a bare field stays bare beside the fixed ones, and the rule still flags it" begin
        text = "struct S\n    x::Real\n    y\nend\n"
        @test abstract_field_fixed(text) == CONCRETE_IMPORT * "@concrete struct S\n    x <: Real\n    y\nend\n"
        @test loaded_abstract_fields(abstract_field_fixed(text), :S) == [:y]
        @test unfixed("struct S\n    y\nend\n")
        @test unfixed("mutable struct S\n    x::Real\n    y\nend\nset!(s) = (s.y = 1)\n")
        @test unfixed("mutable struct S\n    x::Real\n    y\nend\nset!(s) = (s.x = 1)\n")
    end

    @testset "a const field, default, constructor or macro stays: the macro would retype or drop it" begin
        @test unfixed("mutable struct S\n    const x::Real\nend\n")
        @test unfixed("struct S\n    x::Real\n    S(x) = new(x)\nend\n")
        @test unfixed("struct S\n    x::Real\n    function S(x, y)\n        return new(x + y)\n    end\nend\n")
        @test unfixed("struct S\n    x::Real = 1\nend\n")
        @test unfixed("mutable struct S\n    @atomic x::Real\nend\n")
        @test unfixed("Base.@kwdef struct S\n    x::Real = 1\nend\n@concrete struct T\n    y <: Real\nend\n")
    end

    @testset "a struct stays when any reference is not S(...), ::S or <: S" begin
        declaration = "struct S{A}\n    a::A\n    x::Real\nend\n"
        kept = "f(s::S) = s\ng(::S) = S(1, 2)\nh(::Type{T}) where {T <: S} = 1\n"
        @test abstract_field_fixed(declaration * kept) == CONCRETE_IMPORT * replace(declaration, "struct S" => "@concrete struct S", "x::Real" => "x <: Real") * kept
        for use in ("f() = S{Int}(1, 2)\n", "f() = Other.S{Int}\n", "f(s::S{Int}) = s\n", "f(::Type{S}) = 1\n", "f(s) = typeof(s) === S\n", "f(s) = s isa S\n", "T = S\n", "export S\n", "f(x) = [S(x, 1)]::Vector{S}\n", "f() = S\n")
            @test unfixed(declaration * use)
        end
        text = "struct S\n    x::Real\nend\n"
        @test abstract_field_fixed(["a.jl" => text, "b.jl" => "make() = S{Int}(1)\n"]) == Dict("a.jl" => text, "b.jl" => "make() = S{Int}(1)\n")
    end

    @testset "the references the rewrite would break or flip are left alone, and break or flip once rewritten" begin
        declaration = "struct C\n    x::Real\nend\n"
        forced = "using ConcreteStructs: @concrete\n@concrete struct C\n    x <: Real\nend\n"
        function evaluated(text::String, expression::String)::Any
            try
                return Base.include_string(Module(:Evaluated), text * expression)
            catch failure
                throw(failure isa LoadError ? failure.error : failure)
            end
        end
        breaks = ["total(cs::Vector{C}) = sum(c.x for c in cs)\ntotal([C(1)])\n", "total(cs::Dict{Int, C}) = length(cs)\ntotal(Dict(1 => C(1)))\n", "total(cs::Ref{C}) = cs[].x\ntotal(Ref(C(1)))\n", "total(cs::Array{C}) = length(cs)\ntotal([C(1)])\n"]
        for use in breaks
            @test unfixed(declaration * use)
            @test evaluated(declaration, use) isa Real
            @test_throws MethodError evaluated(forced, use)
        end
        flips = ["typeof(C(1)) === C\n", "isconcretetype(C)\n", "try sizeof(C) == sizeof(Int) catch; :incomplete end\n", "haskey(Dict{Any, Int}(C => 1), typeof(C(1)))\n"]
        for use in flips
            @test unfixed(declaration * use)
            @test evaluated(declaration, use) != evaluated(forced, use)
        end
    end

    @testset "without --unsafe-fixes the fixer writes nothing" begin
        tree = write_tree(mktempdir(), ["source.jl" => "struct S\n    x::Real\nend\n"])
        Corset.apply_fix!(Corset.AbstractFieldRule(), Repository(tree), (".",), false)
        @test read(joinpath(tree, "source.jl"), String) == "struct S\n    x::Real\nend\n"
    end

    @testset "a # lint: abstract-field comment on the struct keeps it" begin
        @test unfixed("struct S # lint: abstract-field  erased on purpose\n    x::Real\nend\n")
    end

    @testset "the fixed struct has no abstract field, builds, and the fixer is idempotent" begin
        text = "struct S{E}\n    x::AbstractVector{E}\n    y::E\n    z::Real\nend\n"
        fixed = abstract_field_fixed(text)
        @test loaded_abstract_fields(text, :S) == [:x, :z]
        @test isempty(loaded_abstract_fields(fixed, :S))
        holder = Module(:Built)
        Base.include_string(holder, fixed)
        @test typeof(holder.S([1], 2, 3.0)) == holder.S{Int, Vector{Int}, Float64}
        @test abstract_field_fixed(fixed) == fixed
    end
end

@testset "abstract-field: a mutable struct's written field keeps its type" begin
    declaration = "mutable struct Accepted\n    proposal::AbstractVector{Float32}\n    steps::Integer\nend\n"
    fixed_steps = CONCRETE_IMPORT * "@concrete mutable struct Accepted\n    proposal::AbstractVector{Float32}\n    steps <: Integer\nend\n"
    fixed_both = CONCRETE_IMPORT * "@concrete mutable struct Accepted\n    proposal <: AbstractVector{Float32}\n    steps <: Integer\nend\n"

    @testset "a field never written is a parameter, an element write or broadcast does not count" begin
        @test abstract_field_fixed(declaration * "read(a::Accepted) = a.proposal\n") == fixed_both * "read(a::Accepted) = a.proposal\n"
        reads = "fill!(a::Accepted) = a.proposal .= 0\nwrite(a::Accepted) = a.proposal[1] = 0\n"
        @test abstract_field_fixed(declaration * reads) == fixed_both * reads
    end

    @testset "an assignment, update, setfield!, setproperty! or atomic write stops that field" begin
        for write in ("a.proposal = [1.0f0]", "a.proposal += [1.0f0]", "(a.proposal, other) = (1, 2)", "(a.proposal::Any) = 1", "setfield!(a, :proposal, [1.0f0])", "Base.setproperty!(a, :proposal, [1.0f0])", "@atomic a.proposal = [1.0f0]", "swapfield!(a, :proposal, [1.0f0])")
            tail = "function touch!(a::Accepted)\n    $write\nend\n"
            @test abstract_field_fixed(declaration * tail) == fixed_steps * tail
        end
    end

    @testset "a write elsewhere in the tree counts, and an unnamed field stops every field" begin
        @test abstract_field_fixed(["a.jl" => declaration, "b.jl" => "touch!(a) = (a.steps = 2)\n"])["a.jl"] ==
            CONCRETE_IMPORT * "@concrete mutable struct Accepted\n    proposal <: AbstractVector{Float32}\n    steps::Integer\nend\n"
        for write in ("setfield!(a, name, 1)", "setproperty!(a, 2, 1)")
            @test unfixed(declaration * "touch!(a, name) = $write\n")
        end
        @test abstract_field_fixed(declaration * "touch!(a, name) = setfield!(a, :x)\n") == fixed_both * "touch!(a, name) = setfield!(a, :x)\n"
        quiet = "touch!(a) = f(a)(1).proposal\nmake() = (1).steps\ng(a) = a.(b)\nh(a) = a.x .= 1\n"
        @test abstract_field_fixed(declaration * quiet) == fixed_both * quiet
    end

    @testset "an immutable struct's field is a parameter whatever is assigned to the name" begin
        text = "struct Frozen\n    x::Real\nend\ntouch!(a) = (a.x = 1)\n"
        @test abstract_field_fixed(text) == replace(CONCRETE_IMPORT * text, "struct Frozen\n    x::Real" => "@concrete struct Frozen\n    x <: Real")
    end

    @testset "a parameter pins the type of the first value, which is the failure the fixer avoids" begin
        text = """
        using ConcreteStructs: @concrete
        struct Fill <: AbstractVector{Float32}
            length::Int
        end
        Base.size(fill::Fill)::Tuple{Int} = (fill.length,)
        Base.getindex(::Fill, ::Int)::Float32 = 0.0f0
        mutable struct Redraws
            proposal::AbstractVector{Float32}
        end
        function accept!(redraws::Redraws)::Nothing
            redraws.proposal = Float32[1, 2]
            return nothing
        end
        """
        @test unfixed(text)
        pinned = Module(:Pinned)
        Base.include_string(pinned, replace(text, "mutable struct Redraws\n    proposal::AbstractVector{Float32}" => "@concrete mutable struct Redraws\n    proposal <: AbstractVector{Float32}"))
        @test_throws MethodError pinned.accept!(pinned.Redraws(pinned.Fill(2)))
        holder = Module(:Unpinned)
        Base.include_string(holder, text)
        redraws = holder.Redraws(holder.Fill(2))
        holder.accept!(redraws)
        @test redraws.proposal == Float32[1, 2]
    end
end

@testset "rewritten: edits at one offset land in a fixed order" begin
    insertion(text::String)::Corset.ByteRewrite = Corset.ByteRewrite("f.jl", 3:2, text)
    replacement = Corset.ByteRewrite("f.jl", 3:4, "R")
    @test Corset.rewritten("abcdef", [insertion("1"), insertion("2")]) == "ab12cdef"
    @test Corset.rewritten("abcdef", [insertion("2"), insertion("1")]) == "ab21cdef"
    @test Corset.rewritten("abcdef", [replacement, insertion("1"), insertion("2")]) == "ab12Ref"
    @test Corset.rewritten("abcdef", [insertion("1"), replacement, insertion("2")]) == "ab12Ref"
end

@testset "abstract-field: a bare field of a @concrete struct is flagged, a bounded one is not" begin
    declaration(field::String)::String = "using ConcreteStructs: @concrete\n@concrete struct S\n    $field\n    n::Int\nend\n"
    @test loaded_abstract_fields(declaration("x"), :S) == [:x]
    @test loaded_abstract_fields(declaration("x <: Any"), :S) == [:x]
    @test isempty(loaded_abstract_fields(declaration("x <: Real"), :S))
    @test isempty(loaded_abstract_fields(declaration("x::Int"), :S))
    @test isempty(loaded_abstract_fields("struct S{A}\n    x::A\nend\n", :S))
end

@testset "abstract-field: only --unsafe-fixes runs the fixer" begin
    @test Corset.is_base_abstract(:Real) && !Corset.is_base_abstract(:Any) && !Corset.is_base_abstract(:Int)
    @test Set(Corset.rule_name.(filter(Corset.unsafe_fixable, Corset.RULES))) == Set(["abstract-field"])
    @test !Corset.fixable(Corset.AbstractFieldRule())
    previewed = package_tree("name = \"Demo\"\n", ["src/Demo.jl" => "module Demo\nstruct S\n    x::Real\nend\nend\n"])
    output, code = captured_main(["check", previewed, "--no-load", "--diff", "--unsafe-fixes"])
    @test code == 1 && occursin("+@concrete struct S", output)
    @test !occursin("@concrete", first(captured_main(["check", previewed, "--no-load", "--diff"])))
    @test_throws ArgumentError Corset.run_rules(Corset.load_config(previewed), previewed; unsafe = true)
end

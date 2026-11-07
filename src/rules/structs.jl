# Rules on the structs a package defines: abstract and union fields, and field names that repeat a word.

"""Struct types `mod`'s package defines, closures excluded; a type bound to two names counts once."""
function module_structs(mod::Module)::Vector{DataType}
    package = Package(mod)
    structs = DataType[Base.unwrap_unionall(value) for value in package_bindings(package) if is_struct_binding(value)]
    return unique(structs[belongs.(parentmodule.(structs), (package,))])
end

"""Whether binding `value` is a struct type, closures excluded."""
is_struct_binding(@nospecialize(value::Any))::Bool = value isa Type && !is_closure_type(value) &&
    Base.unwrap_unionall(value) isa DataType && isstructtype(Base.unwrap_unionall(value))

"""The `module_structs` of `mod` declared mutable."""
mutable_structs(mod::Module)::Vector{DataType} = filter(ismutabletype, module_structs(mod))

"""
Fields of `type` declared with an abstract type (not a type parameter), a `Union` of two or more
types besides `Nothing` and `Missing`, or a concrete container of either: `Vector{Any}`,
`Base.RefValue{Any}` and `Dict{Tuple, Any}` are concrete, but every read from them is dynamically
dispatched, and a `Union{Float32, Float64}` field leaves each read a union a parameter would fix.
"""
function abstract_fields(type::DataType)::Vector{Symbol}
    field_names = collect(Symbol, fieldnames(type))
    return field_names[abstract_declaration.(fieldtype.((type,), field_names))]
end

"""Whether field type `declared` is abstract: not a type parameter, and `union_holds_abstract` for a `Union`, `holds_abstract` for any other type."""
abstract_declaration(@nospecialize(declared::Any))::Bool =
    !(declared isa TypeVar) && (declared isa Union ? union_holds_abstract(declared) : holds_abstract(declared))

"""Whether `type` is one of the types a `Union` adds for an absent value, which a field may hold: `Nothing` and `Missing`."""
absent_value(type::Any)::Bool = type === Nothing || type === Missing

"""
Whether the `Union` `declared` lists two or more members besides `Nothing` and `Missing`
(`Union{Float32, Float64}`, `Union{T, Int}`), or one that `holds_abstract` (`Union{Nothing, Real}`).
`Union{Nothing, Float64}` and `Union{Missing, T}` hold an absent value or one type, and pass.
"""
function union_holds_abstract(declared::Union)::Bool # lint: abstract-local  a Union's members are types and type variables
    members = filter(!absent_value, Base.uniontypes(declared)) # lint: non-public-access  Base has no public accessor for a Union's members
    return length(members) >= 2 || any(member -> member isa Type && holds_abstract(member), members)
end

"""
Whether `declared` is abstract or has an abstract type among its parameters, at any depth.
Allowed: a `Union` that `union_holds_abstract` passes, `Type{T}`, a struct's own type parameters
(`Vector{E}` with `E` free), and value parameters (`SVector{16, E}`'s `Tuple{16}`).
"""
function holds_abstract(declared::Type)::Bool # lint: abstract-local  reflects on values of unknown type
    plain = Base.unwrap_unionall(declared)
    abstract_itself = if Base.has_free_typevars(declared) || plain <: Tuple
        plain isa DataType && isabstracttype(plain)
    else
        !isconcretetype(declared)
    end
    return abstract_itself || any(abstract_parameter, plain.parameters)
end

abstract_parameter(parameter::Any)::Bool = parameter isa UnionAll ||
    (parameter isa Union && union_holds_abstract(parameter)) ||
    (parameter isa DataType && !(parameter <: Type) && holds_abstract(parameter))

"""First word of a name in snake case: `SolverControls` and `solver_tolerance` both give `"solver"`."""
first_word(name::Symbol)::String = lowercase(
    first(
        split(
            replace(string(name), r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])" => "_"),
            '_',
        )
    )
)

"""
    repeated_prefix(type)

The word that the field names of `type` repeat instead of saying it once in the type:
the type's own first word starting any field (`SolverControls.solver_tolerance`), or one
first word shared by more than half of at least three fields (`continuation_step`,
`continuation_theta`, ...: those fields belong in a `ContinuationControls`). `nothing`
when no word repeats.
"""
function repeated_prefix(type::DataType)::Union{String, Nothing} # lint: abstract-local  reflects on values of unknown type
    words = String[first_word(name) for name in collect(Symbol, fieldnames(type)) if occursin('_', string(name))]
    own = first_word(nameof(type))
    if own in words
        return own
    end
    fields = fieldcount(type)
    candidates = unique(words)
    shared = candidates[count.(isequal.(candidates), (words,)) .* 2 .> fields]
    if fields >= 3 && !isempty(shared)
        return only(shared)
    end
    return nothing
end

# Rules on the structs a package defines: abstract fields, and field names that repeat a word.

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
Fields of `type` declared with an abstract type (not a type parameter, not a `Union`), or
with a concrete container of one: `Vector{Any}`, `Base.RefValue{Any}` and
`Dict{Tuple, Any}` are concrete, but every read from them is dynamically dispatched.
"""
function abstract_fields(type::DataType)::Vector{Symbol}
    field_names = collect(Symbol, fieldnames(type))
    return field_names[abstract_declaration.(fieldtype.((type,), field_names))]
end

"""Whether field type `declared` is abstract: not a type parameter, not a `Union`, and `holds_abstract`."""
abstract_declaration(@nospecialize(declared::Any))::Bool = !(declared isa TypeVar) && !(declared isa Union) && holds_abstract(declared)

"""
Whether `declared` is abstract or has an abstract type among its parameters, at any depth.
Allowed: `Union`s (small, split by the compiler), `Type{T}`, a struct's own type parameters
(`Vector{E}` with `E` free), and value parameters (`SVector{16, E}`'s `Tuple{16}`).
"""
function holds_abstract(declared::Type)::Bool # lint: unstable-variable  reflects on values of unknown type
    plain = Base.unwrap_unionall(declared)
    abstract_itself = if Base.has_free_typevars(declared) || plain <: Tuple
        plain isa DataType && isabstracttype(plain)
    else
        !isconcretetype(declared)
    end
    return abstract_itself || any(abstract_parameter, plain.parameters)
end

abstract_parameter(parameter::Any)::Bool = parameter isa UnionAll ||
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
function repeated_prefix(type::DataType)::Union{String, Nothing} # lint: unstable-variable  reflects on values of unknown type
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

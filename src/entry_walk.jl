# The frames an entry point compiles, found by walking optimized IR along `:invoke` edges.
# `inferred_methods` filters them for the rules, which read the same IR (`runtime_dispatches`).

"""
    mentions_module(signature, target, depth)

Whether `signature` names a type defined in `target` anywhere in its parameters.
"""
function mentions_module(signature::Any, target::Module, depth::Integer)::Bool
    if depth > 6
        return false
    elseif signature isa UnionAll
        return mentions_module(signature.body, target, depth + 1)
    elseif signature isa Union
        return mentions_module(signature.a, target, depth + 1) ||
            mentions_module(signature.b, target, depth + 1)
    elseif !(signature isa DataType)
        return false
    end
    return parentmodule(signature) === target ||
        any(mentions_module.(collect(signature.parameters), (target,), depth + 1))
end

"""
    invoked_instance(callee)

The method instance an `:invoke` statement names: a `CodeInstance` on Julia 1.12 and later.
"""
invoked_instance(callee::Core.MethodInstance)::Core.MethodInstance = callee
invoked_instance(callee::Core.CodeInstance)::Union{Nothing, Core.MethodInstance} = invoked_instance(callee.def)
invoked_instance(::Any)::Nothing = nothing

"""
    frame_callees(ir, target)

The signatures `ir`, an optimized method body, calls through `:invoke` edges and a walk of `target`
follows: callees defined in `target` or whose signature names one of its types (JET's `target_modules`
scope).
"""
function frame_callees(ir::COMPILER.IRCode, target::Module)::Vector{Type}
    expressions = [statement for statement in ir.stmts.stmt if statement isa Expr]
    invoked = [invoked_instance(first(statement.args)) for statement in expressions if statement.head in (:invoke, :invoke_modify)]
    return Type[callee.specTypes for callee in filter(Base.Fix2(followed, target), invoked)]
end

"""Whether a walk of `target` follows `callee`, an `invoked_instance`: a method of `target`, or one whose signature names a type of it."""
followed(callee::Any, target::Module)::Bool = callee isa Core.MethodInstance && callee.def isa Method &&
    (callee.def.module === target || mentions_module(callee.specTypes, target, 0))

"""
    entry_frames(seeds, target)

The `typed_frames` of every signature reachable from `seeds` (entry-point call signatures such as
`Tuple{typeof(f), Int}`) along `frame_callees` edges, the seeds included; empty where inference yields
none. Pass them to `inferred_methods`, which then infers nothing again.
"""
function entry_frames(seeds::AbstractVector{<:Type}, target::Module)::Dict{Type, Vector{Inferred}}
    frames = Dict{Type, Vector{Inferred}}()
    frontier = unique(Type[seeds...])
    while !isempty(frontier)
        for signature in frontier
            frames[signature] = typed_frames(signature)
        end
        frontier = new_callees(frames, frontier, target)
    end
    return frames
end

"""The signatures the `frontier` frames call that `frames` does not hold yet."""
new_callees(frames::AbstractDict{Type}, frontier::AbstractVector{<:Type}, target::Module)::Vector{Type} = unique(
    filter(!Base.Fix1(haskey, frames), reduce(vcat, signature_callees.((frames,), frontier, (target,)); init = Type[])),
)

"""The signatures the `frames` of `signature` call (`frame_callees`)."""
signature_callees(frames::AbstractDict{Type}, signature::Type, target::Module)::Vector{Type} =
    reduce(vcat, frame_callees.(getfield.(frames[signature], :ir), (target,)); init = Type[])

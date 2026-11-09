# The rule `abstract-element`: a container built with an abstract element (or key or value) type stores every
# element boxed, and inference loses the element type. `Vector{Real}()`, `Dict{String, Any}()`, `Real[]` and
# `similar(x, Real)` take a concrete type, or a type parameter the caller fixes.

# The number of type parameters, counted from the first, that name what a container holds.
const ELEMENT_PARAMETERS = (Vector = 1, Matrix = 1, Array = 1, Set = 1, Dict = 2, OrderedDict = 2, IdDict = 2)

# Syntax kinds of an array literal or comprehension that a type prefixes: `T[…]`, `T[a b]`, `T[a; b]`, `T[x for …]`.
const TYPED_LITERAL_KINDS = (
    SYNTAX.@K_str("ref"), SYNTAX.@K_str("typed_hcat"), SYNTAX.@K_str("typed_vcat"), SYNTAX.@K_str("typed_ncat"),
    SYNTAX.@K_str("typed_comprehension"),
)

"""One construction of a container with an abstract element type: its syntax `node` and the `type` text that is abstract."""
struct AbstractElementUse
    node::SYNTAX.SyntaxNode
    type::String
end

"""Whether the binding `found` is a type that is abstract (`curly`: its parameters are what the syntax chooses) or not concrete (bare)."""
abstract_binding(found::Type, curly::Bool)::Bool = found === Type ? false : curly ? isabstracttype(found) : non_concrete(found)
abstract_binding(::Any, ::Bool)::Bool = false

"""Whether type `found` is not concrete, or is a `Union` with a member that is not."""
non_concrete(found::Type)::Bool = found isa Union ? non_concrete(found.a) || non_concrete(found.b) : !isconcretetype(found)

"""
Whether the type syntax `node` names a type that is not concrete in `scope`: an abstract type or a bare parametric
one (`Real`, `Vector`), or a `Union` with such a member. `Union{Nothing, Int}` and `Vector{Int}` are concrete, and
so is `Type`, whose elements are type objects that carry no element type to infer. Only a name is looked up; no code runs.
"""
function names_abstract_type(node::SYNTAX.SyntaxNode, scope::Module)::Bool
    parts = node_children(node)
    curly = SYNTAX.kind(node) === CURLY_KIND
    head = curly ? first(parts) : node
    name = Symbol(callee_name(head))
    if curly && name === :Union
        return any(Base.Fix2(names_abstract_type, scope), parts[2:end])
    end
    return isdefined(scope, name) && abstract_binding(getglobal(scope, name), curly)
end

"""Whether the type syntax `node` is a container such as `Vector{Real}` whose element, key or value parameter is abstract."""
function has_abstract_element(node::SYNTAX.SyntaxNode, scope::Module)::Bool
    parts = node_children(node)
    if SYNTAX.kind(node) !== CURLY_KIND || isempty(parts)
        return false
    end
    count = get(ELEMENT_PARAMETERS, Symbol(callee_name(first(parts))), 0)
    return any(Base.Fix2(names_abstract_type, scope), parts[2:min(end, 1 + count)])
end

"""Whether syntax `argument` of `similar` is an abstract element type, or a container type with an abstract element."""
similar_type(argument::SYNTAX.SyntaxNode, scope::Module)::Bool = has_abstract_element(argument, scope) || names_abstract_type(argument, scope)

"""The syntax nodes of the `similar(array, T, …)` call `node` that name a container type with an abstract element, empty for any other node."""
function similar_types(node::SYNTAX.SyntaxNode, scope::Module)::Vector{SYNTAX.SyntaxNode}
    arguments = filter(!keyword_part, node_children(node)[2:end])
    return filter(Base.Fix2(similar_type, scope), arguments[1:min(end, 2)])
end

"""The use at syntax `node` whose abstract type is written by syntax `type`."""
use_of(node::SYNTAX.SyntaxNode, type::SYNTAX.SyntaxNode)::AbstractElementUse = AbstractElementUse(node, SYNTAX.sourcetext(type))

"""The abstract-element constructions at or below syntax `node` in `scope`, in source order."""
function abstract_element_uses(node::SYNTAX.SyntaxNode, scope::Module)::Vector{AbstractElementUse}
    parts = node_children(node)
    kind = SYNTAX.kind(node)
    found = AbstractElementUse[]
    if kind === CALL_KIND && is_prefix_call(node) && !isempty(parts)
        if has_abstract_element(first(parts), scope)
            push!(found, AbstractElementUse(node, SYNTAX.sourcetext(first(parts))))
        elseif call_name(node) == "similar"
            append!(found, map(Base.Fix1(use_of, node), similar_types(node, scope)))
        end
    elseif kind in TYPED_LITERAL_KINDS && !isempty(parts) && names_abstract_type(first(parts), scope)
        push!(found, AbstractElementUse(node, SYNTAX.sourcetext(first(parts))))
    end
    for part in parts
        append!(found, abstract_element_uses(part, scope))
    end
    return found
end

"""The sites of the Julia file `source` that build a container of an abstract element type, resolving type names in `scope`."""
function abstract_elements(source::Source, scope::Module)::Vector{Site}
    (; path, name, tree) = source
    return [
        Site(name, path, first(SYNTAX.source_location(use.node)), "`$(use.type)` is not concrete, so the container boxes every element; name a concrete type or a type parameter")
            for use in abstract_element_uses(tree, scope)
    ]
end

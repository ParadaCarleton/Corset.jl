# The fixer of `literal-array`: `C{T}(undef, length(x))` and `similar(C{T}, size(x))` take
# `similar(x, T, …)` when `x` is an array parameter of the enclosing method that the body never rebinds.

# Parameter type names that make a parameter an array.
const ARRAY_PARAMETER_TYPES = (
    "Vector", "Matrix", "Array", "AbstractVector", "AbstractMatrix", "AbstractArray", "StridedVector", "StridedMatrix", "StridedArray",
    "DenseVector", "DenseMatrix", "DenseArray",
)

"""The signature call of the method that defines syntax `node`, as a vector that is empty when `node` is in no method."""
function enclosing_signatures(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    current = node.parent
    while !isnothing(current)
        if SYNTAX.kind(current) === SYNTAX.@K_str("function") || (SYNTAX.kind(current) === SYNTAX.@K_str("=") && !isempty(node_children(current)))
            signature = first(node_children(current))
            while SYNTAX.kind(signature) in (SYNTAX.@K_str("where"), SYNTAX.@K_str("::")) && !isempty(node_children(signature))
                signature = first(node_children(signature))
            end
            if SYNTAX.kind(signature) === CALL_KIND
                return [signature]
            elseif SYNTAX.kind(current) === SYNTAX.@K_str("function")
                return SYNTAX.SyntaxNode[]
            end
        end
        current = current.parent
    end
    return SYNTAX.SyntaxNode[]
end

"""Whether `signature` annotates its parameter `name` with an array type (`x::AbstractVector{T}`)."""
function array_parameter(signature::SYNTAX.SyntaxNode, name::String)::Bool
    for parameter in node_children(signature)[2:end]
        parts = node_children(parameter)
        if SYNTAX.kind(parameter) === SYNTAX.@K_str("::") && length(parts) == 2 && is_identifier(first(parts), name)
            annotation = last(parts)
            return callee_name(SYNTAX.kind(annotation) === SYNTAX.@K_str("curly") ? first(node_children(annotation)) : annotation) in ARRAY_PARAMETER_TYPES
        end
    end
    return false
end

"""Whether the left-hand side `target` of an assignment binds `name` (`x`, `x::T`, or `x` inside a tuple)."""
function binds_name(target::SYNTAX.SyntaxNode, name::String)::Bool
    return is_identifier(target, name) || (SYNTAX.kind(target) in (SYNTAX.@K_str("::"), SYNTAX.@K_str("tuple"), SYNTAX.@K_str("parameters")) && any(Base.Fix2(binds_name, name), node_children(target)))
end

"""Whether syntax `node` or anything below it assigns, loops over, updates or binds as a lambda, `do` or `catch` variable `name`."""
function rebinds_name(node::SYNTAX.SyntaxNode, name::String)::Bool
    children = node_children(node)
    binders = (SYNTAX.@K_str("="), SYNTAX.@K_str("op="), SYNTAX.@K_str("in"), SYNTAX.@K_str("->"), SYNTAX.@K_str("do"), SYNTAX.@K_str("catch"), SYNTAX.@K_str("function"))
    return (SYNTAX.kind(node) in binders && !isempty(children) && binds_name(first(children), name)) || any(Base.Fix2(rebinds_name, name), children)
end

"""Whether the method defined by `signature` rebinds its parameter `name` in its body."""
function parameter_rebound(signature::SYNTAX.SyntaxNode, name::String)::Bool
    definition = signature.parent
    while !isnothing(definition) && !(SYNTAX.kind(definition) in (SYNTAX.@K_str("function"), SYNTAX.@K_str("=")))
        definition = definition.parent
    end
    return !isnothing(definition) && any(Base.Fix2(rebinds_name, name), node_children(definition)[2:end])
end

"""The array `x` when syntax `dimension` is `length(x)` or `size(x)`, as a vector that is empty otherwise."""
function sized_array(dimension::SYNTAX.SyntaxNode)::Vector{String}
    if SYNTAX.kind(dimension) === CALL_KIND && is_prefix_call(dimension) && call_name(dimension) in ("length", "size")
        arguments = node_children(dimension)[2:end]
        if length(arguments) == 1 && SYNTAX.kind(only(arguments)) === IDENTIFIER_KIND
            return [String(SYNTAX.sourcetext(only(arguments)))]
        end
    end
    return String[]
end

"""Whether syntax `node` is the right-hand side of an assignment to a typed local (`x::Vector{T} = …`), whose type a template may not keep."""
function typed_local(node::SYNTAX.SyntaxNode)::Bool
    parent = node.parent
    return !isnothing(parent) && SYNTAX.kind(parent) === SYNTAX.@K_str("=") && SYNTAX.kind(first(node_children(parent))) === SYNTAX.@K_str("::")
end

"""The replacement text for the literal-array call `node` as a vector, empty when no array parameter sizes it."""
function similar_replacement(node::SYNTAX.SyntaxNode)::Vector{String}
    parts = node_children(node)
    arguments = filter(!keyword_part, parts[2:end])
    head = call_name(node) == "similar" ? first(arguments) : first(parts)
    signatures = enclosing_signatures(node)
    if SYNTAX.kind(head) !== SYNTAX.@K_str("curly") || length(node_children(head)) < 2 || length(arguments) != 2 || length(arguments) != length(parts) - 1 || isempty(signatures) || typed_local(node)
        return String[]
    end
    for name in sized_array(last(arguments))
        signature = only(signatures)
        if array_parameter(signature, name) && !parameter_rebound(signature, name)
            return ["similar($name, $(SYNTAX.sourcetext(node_children(head)[2])), $(SYNTAX.sourcetext(last(arguments))))"]
        end
    end
    return String[]
end

"""The repairs below syntax `node` of `source`: one per literal-array call a parameter sizes."""
function literal_array_repairs!(repairs::AbstractVector{Repair{ByteRewrite}}, source::Source, node::SYNTAX.SyntaxNode)::Nothing
    if SYNTAX.kind(node) === CALL_KIND && !isempty(literal_array_detail(node))
        for text in similar_replacement(node)
            push!(repairs, Repair(Site(source.name, source.path, first(SYNTAX.source_location(node)), ""), ByteRewrite(source.path, SYNTAX.byte_range(node), text)))
        end
    end
    for child in node_children(node)
        literal_array_repairs!(repairs, source, child)
    end
    return nothing
end

"""
    literal_array_plan(repository, directories)

The `FixPlan` that rewrites each `C{T}(undef, length(x))` and `similar(C{T}, size(x))` as `similar(x, T, length(x))`
and `similar(x, T, size(x))`, where `x` is a parameter annotated as an array that the body never rebinds and the
call is no typed local's value. The result takes `x`'s array type: a sparse `x` makes it sparse.
"""
function literal_array_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)}
    repairs = Repair{ByteRewrite}[]
    for source in directory_sources(repository, directories)
        literal_array_repairs!(repairs, source, source.tree)
    end
    return FixPlan(repairs, rewritten_texts)
end

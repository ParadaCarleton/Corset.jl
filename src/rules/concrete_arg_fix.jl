# The fixer of `concrete-arg`: an argument annotated `Vector{T}`, `Matrix{T}`, `Array{T, N}` or
# `Dict{K, V}` that the method never resizes takes `AbstractVector{T}` and its siblings instead.

const ABSTRACT_CONTAINERS = (Vector = "AbstractVector", Matrix = "AbstractMatrix", Array = "AbstractArray", Dict = "AbstractDict")

"""The annotated arguments of call syntax `call` as (name, annotation) pairs; keyword arguments and splats included."""
function annotated_argument_nodes(call::SYNTAX.SyntaxNode)::Vector{Tuple{SYNTAX.SyntaxNode, SYNTAX.SyntaxNode}}
    pairs = Tuple{SYNTAX.SyntaxNode, SYNTAX.SyntaxNode}[]
    for argument in node_children(call)[2:end]
        for inner in (SYNTAX.kind(argument) === PARAMETERS_KIND ? node_children(argument) : [argument])
            unwrapped = inner
            while SYNTAX.kind(unwrapped) in (KEYWORD_KIND, SYNTAX.@K_str("..."))
                unwrapped = first(node_children(unwrapped))
            end
            parts = node_children(unwrapped)
            if SYNTAX.kind(unwrapped) === SYNTAX.@K_str("::") && length(parts) == 2
                push!(pairs, (first(parts), last(parts)))
            end
        end
    end
    return pairs
end

"""The signature call inside syntax `signature`, below any `where` or return annotation, as a vector of one node, or of none for a definition without arguments."""
function signature_call_nodes(signature::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    while SYNTAX.kind(signature) in (SYNTAX.@K_str("where"), SYNTAX.@K_str("::"))
        signature = first(node_children(signature))
    end
    return SYNTAX.kind(signature) === CALL_KIND ? [signature] : SYNTAX.SyntaxNode[]
end

"""The (range, text) rewrites that make the container names of annotation syntax `annotation` abstract: a bare or curly head, or the members of a `Union`."""
function abstract_container_edits(annotation::SYNTAX.SyntaxNode)::Vector{Tuple{UnitRange{Int}, String}}
    if SYNTAX.kind(annotation) === IDENTIFIER_KIND
        replacement = get(ABSTRACT_CONTAINERS, Symbol(SYNTAX.sourcetext(annotation)), "")
        return isempty(replacement) ? Tuple{UnitRange{Int}, String}[] : [(SYNTAX.byte_range(annotation), replacement)]
    elseif SYNTAX.kind(annotation) === SYNTAX.@K_str("curly")
        head, members = Iterators.peel(node_children(annotation))
        if is_identifier(head, "Union")
            return Tuple{UnitRange{Int}, String}[edit for member in members for edit in abstract_container_edits(member)]
        end
        return abstract_container_edits(head)
    end
    return Tuple{UnitRange{Int}, String}[]
end

"""Every `function` or short-form definition node under syntax `node`."""
function definition_nodes(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    found = SYNTAX.SyntaxNode[found for child in node_children(node) for found in definition_nodes(child)]
    return SYNTAX.kind(node) === SYNTAX.@K_str("function") ? vcat([node], found) : found
end

"""The repairs of the Julia file `source`: one per container annotation of an argument the method does not resize."""
function concrete_arg_repairs(source::Source)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for definition in definition_nodes(source.tree)
        parts = node_children(definition)
        body = Expr(:block, Expr(last(parts)))
        for call in signature_call_nodes(first(parts)), (name, annotation) in annotated_argument_nodes(call)
            if resizes(body, Symbol(SYNTAX.sourcetext(name)))
                continue
            end
            line = first(SYNTAX.source_location(definition))
            for (range, replacement) in abstract_container_edits(annotation)
                push!(repairs, Repair(Site(source.name, source.path, line, ""), ByteRewrite(source.path, range, replacement)))
            end
        end
    end
    return repairs
end

"""
    concrete_arg_plan(repository, directories)

The `FixPlan` that writes the concrete container annotations of arguments a method never resizes as their abstract forms.
"""
concrete_arg_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)} =
    FixPlan(collect(Repair{ByteRewrite}, Iterators.flatten(concrete_arg_repairs.(directory_sources(repository, directories)))), rewritten_texts)

# The rule `similar-array`: an array is built with `similar(template, T, dims)`, which keeps the template's
# storage (GPU, sparse), instead of naming a concrete container (`Vector{T}(undef, n)`, `Matrix{T}(undef, …)`,
# `Array{T}(undef, …)`, `Vector{T}(x)`). Exempt: the empty growable forms `T[]` and `Vector{T}()` (no template),
# `Matrix{T}(I, n, n)` and filled forms (more than one argument), and an untyped `Array(x)` (a host transfer).
# `similar_array_plan` rewrites an `undef` constructor sized by `length(x)` or `size(x)`; `--fix` does not run it,
# because a sparse or device template changes the result's type (see `similar_array_plan`).

# Parameter type names that make a variable an array.
const ARRAY_TYPES = (
    "Vector", "Matrix", "Array", "AbstractVector", "AbstractMatrix", "AbstractArray", "StridedVector", "StridedMatrix", "StridedArray",
    "DenseVector", "DenseMatrix", "DenseArray",
)

# Calls whose first argument is a buffer written from elsewhere, whose storage the source array may not share.
const COPY_NAMES = ("copyto!", "copy!", "unsafe_copyto!")

# Container names that build a concrete array.
const CONTAINER_NAMES = ("Vector", "Matrix", "Array")

# Dimension calls whose argument is a template array.
const EXTENT_NAMES = ("length", "size")

"""
One construction of a concrete array: its syntax `node`, the `form` (`:undef` for `C{T}(undef, dims…)`, `:conversion` for `C(x)`; the empty growable forms `T[]` and `C{T}()` have no template to mirror and are not constructions), the `element` type text and, for `:undef`, the `template` variable and `extent` call it is sized by.
"""
struct ArrayConstruction
    node::SYNTAX.SyntaxNode
    form::Symbol
    element::String
    template::String
    dimension::String
end

"""The signature call syntax of the function definition that contains `node`, as a vector that is empty when there is none."""
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
            end
        end
        current = current.parent
    end
    return SYNTAX.SyntaxNode[]
end

"""Whether the enclosing function annotates the parameter `variable` with an array type (`x::AbstractVector{T}`)."""
function annotated_array(node::SYNTAX.SyntaxNode, variable::String)::Bool
    parameters = [parameter for signature in enclosing_signatures(node) for parameter in node_children(signature)[2:end]]
    for parameter in parameters
        if SYNTAX.kind(parameter) === SYNTAX.@K_str("::") && length(node_children(parameter)) == 2 && is_identifier(first(node_children(parameter)), variable)
            annotation = last(node_children(parameter))
            return callee_name(SYNTAX.kind(annotation) === SYNTAX.@K_str("curly") ? first(node_children(annotation)) : annotation) in ARRAY_TYPES
        end
    end
    return false
end

"""Whether the construction `node` is bound to a variable that a `copyto!`, `copy!` or `unsafe_copyto!` call fills."""
function copy_destination(node::SYNTAX.SyntaxNode)::Bool
    parent = node.parent
    if isnothing(parent) || SYNTAX.kind(parent) !== SYNTAX.@K_str("=") || SYNTAX.kind(first(node_children(parent))) !== IDENTIFIER_KIND
        return false
    end
    buffer = String(SYNTAX.sourcetext(first(node_children(parent))))
    scopes = enclosing_scope(parent)
    return !isempty(scopes) && any(copy_target, variable_reads(only(scopes), buffer))
end

"""Whether the variable read `read` is the destination (first argument) of a copy call."""
function copy_target(read::SYNTAX.SyntaxNode)::Bool
    call = read.parent
    return !isnothing(call) && SYNTAX.kind(call) === CALL_KIND && is_prefix_call(call) && call_name(call) in COPY_NAMES && node_children(call)[2] === read
end

"""Whether the lhs syntax `target` of an assignment binds `variable` (`x`, `x::T`, or `x` inside a tuple)."""
function binds_name(target::SYNTAX.SyntaxNode, variable::String)::Bool
    if is_identifier(target, variable)
        return true
    end
    return SYNTAX.kind(target) in (SYNTAX.@K_str("::"), SYNTAX.@K_str("tuple"), SYNTAX.@K_str("parameters")) && any(Base.Fix2(binds_name, variable), node_children(target))
end

"""Whether the syntax `node` or anything below it assigns, loops over or updates the name `variable`."""
function rebinds_name(node::SYNTAX.SyntaxNode, variable::String)::Bool
    children = node_children(node)
    assigns = SYNTAX.kind(node) in (SYNTAX.@K_str("="), SYNTAX.@K_str("op="), SYNTAX.@K_str("in")) && !isempty(children) && binds_name(first(children), variable)
    return assigns || any(Base.Fix2(rebinds_name, variable), children)
end

"""Whether the function that defines the signature `signature` assigns to the parameter `variable` in its body."""
function parameter_rebound(signature::SYNTAX.SyntaxNode, variable::String)::Bool
    definition = signature.parent
    while !isnothing(definition) && !(SYNTAX.kind(definition) in (SYNTAX.@K_str("function"), SYNTAX.@K_str("=")))
        definition = definition.parent
    end
    return !isnothing(definition) && any(Base.Fix2(rebinds_name, variable), node_children(definition)[2:end])
end

"""Whether the template `variable` of the construction `node` is an annotated array parameter that the body never rebinds, and the buffer is no copy destination."""
function similar_is_safe(node::SYNTAX.SyntaxNode, variable::String)::Bool
    signatures = isempty(variable) ? SYNTAX.SyntaxNode[] : enclosing_signatures(node)
    return !isempty(signatures) && annotated_array(node, variable) && !parameter_rebound(only(signatures), variable) && !copy_destination(node)
end

"""The container name and element type text of constructor callee `head` (`Vector{T}` gives `("Vector", "T")`, `Matrix` gives `("Matrix", "")`), or an empty name when it is no container."""
function container_of(head::SYNTAX.SyntaxNode)::Tuple{String, String}
    if SYNTAX.kind(head) === SYNTAX.@K_str("curly")
        parts = node_children(head)
        name = callee_name(first(parts))
        return name in CONTAINER_NAMES ? (name, length(parts) == 2 ? String(SYNTAX.sourcetext(parts[2])) : "") : ("", "")
    end
    name = callee_name(head)
    return name in CONTAINER_NAMES ? (name, "") : ("", "")
end

"""The variable `x` when `dimension` is `length(x)` or `size(x)`, else `""`."""
function extent_template(dimension::SYNTAX.SyntaxNode)::String
    if SYNTAX.kind(dimension) === CALL_KIND && is_prefix_call(dimension) && call_name(dimension) in EXTENT_NAMES
        arguments = node_children(dimension)[2:end]
        return length(arguments) == 1 && SYNTAX.kind(only(arguments)) === IDENTIFIER_KIND ? String(SYNTAX.sourcetext(only(arguments))) : ""
    end
    return ""
end

"""The `ArrayConstruction` that syntax `node` is, as a vector that is empty when it is none."""
function node_constructions(node::SYNTAX.SyntaxNode)::Vector{ArrayConstruction}
    parts = node_children(node)
    if SYNTAX.kind(node) !== CALL_KIND || !is_prefix_call(node)
        return ArrayConstruction[]
    end
    container, element = container_of(first(parts))
    arguments = filter(!keyword_part, parts[2:end])
    host_transfer = container == "Array" && isempty(element)
    if isempty(container) || isempty(arguments) || host_transfer
        return ArrayConstruction[]
    elseif !is_identifier(first(arguments), "undef")
        return length(arguments) == 1 ? [ArrayConstruction(node, :conversion, element, "", String(SYNTAX.sourcetext(only(arguments))))] : ArrayConstruction[]
    end
    template = length(arguments) == 2 && !isempty(element) ? extent_template(last(arguments)) : ""
    safe = similar_is_safe(node, template)
    return [ArrayConstruction(node, :undef, element, safe ? template : "", safe ? String(SYNTAX.sourcetext(last(arguments))) : "")]
end

"""Every array construction below syntax `node`, in source order."""
function array_constructions(node::SYNTAX.SyntaxNode)::Vector{ArrayConstruction}
    found = node_constructions(node)
    for child in node_children(node)
        append!(found, array_constructions(child))
    end
    return found
end

"""The text that replaces the fixable `construction`: `similar(x, T, dims)`, with the constructor's own dimensions."""
similar_text(construction::ArrayConstruction)::String = "similar($(construction.template), $(construction.element), $(construction.dimension))"

"""The site of `construction` in `source`, with the replacement it offers or why it has none."""
function similar_array_site(source::Source, construction::ArrayConstruction)::Site
    node = construction.node
    first_line = first(SYNTAX.source_location(node))
    last_line = first(SYNTAX.source_location(node.source, last(SYNTAX.byte_range(node))))
    advice = if !isempty(construction.template)
        "use `$(similar_text(construction))`"
    elseif construction.form === :undef
        "no array known to be one (a parameter annotated as an array) sizes it, or its buffer is a copy destination; build it with `similar(x, T, dims)` of an array whose storage it should follow"
    else
        "a conversion copies into a concrete container; use `$(isempty(construction.element) ? "collect($(construction.dimension))" : "collect($(construction.element), $(construction.dimension))")`"
    end
    return Site(source.name, source.path, first_line, last_line, "`$(SYNTAX.sourcetext(node))` names a concrete array type: $advice")
end

"""One site per array construction (`array_constructions`)."""
function similar_array_sites(sources::AbstractVector{Source})::Vector{Site}
    sites = Site[]
    for source in sources
        for construction in array_constructions(source.tree)
            push!(sites, similar_array_site(source, construction))
        end
    end
    return sites
end

"""The repairs of `source`: one per `undef` construction with a template."""
function similar_array_repairs(source::Source)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for construction in array_constructions(source.tree)
        if !isempty(construction.template)
            push!(repairs, Repair(similar_array_site(source, construction), ByteRewrite(source.path, SYNTAX.byte_range(construction.node), similar_text(construction))))
        end
    end
    return repairs
end

"""
    similar_array_plan(repository, directories)

The `FixPlan` that rewrites each `C{T}(undef, length(x))` or `C{T}(undef, size(x))` as `similar(x, T, length(x))` or
`similar(x, T, size(x))`, where `x` is a parameter annotated as an array that the body never rebinds and the buffer is
no `copyto!` destination. `corset --fix` does not run it: review its diff. Two limits no annotation can exclude: a
sparse `x` makes the result sparse, and a buffer that a helper fills (`transfer!(buffer, data)`) can become device memory.
"""
function similar_array_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)}
    repairs = Repair{ByteRewrite}[]
    for source in directory_sources(repository, directories)
        append!(repairs, similar_array_repairs(source))
    end
    return FixPlan(repairs, rewritten_texts)
end

# The rule `type-disruption`: code that drops the types its inputs carry. Its sub-checks (`float-widening`,
# `float64`, `literal-array`) keep their own names for levels, baselines and `# lint:` comments.
# See `docs/src/rules.md`.

# Container names that build a concrete array.
const ARRAY_CONTAINERS = ("Vector", "Matrix", "Array")

"""Whether callee syntax `head` names a literal array container: `Vector`, `Matrix` or `Array`, with or without type parameters."""
function literal_container(head::SYNTAX.SyntaxNode)::Bool
    if SYNTAX.kind(head) === SYNTAX.@K_str("curly")
        return literal_container(first(node_children(head)))
    end
    return callee_name(head) in ARRAY_CONTAINERS
end

"""
The detail of call syntax `node` when it builds an array from a literal container type, else none:
`C{T}(undef, dims…)` and `similar(C{T}, dims…)` for `C` in `Vector`, `Matrix`, `Array`. A template
(`similar(x, T, dims…)`, `similar(A, dims…)` with `A` a type passed in) is allowed.
"""
function literal_array_detail(node::SYNTAX.SyntaxNode)::Vector{String}
    if !is_prefix_call(node)
        return String[]
    end
    parts = node_children(node)
    arguments = filter(!keyword_part, parts[2:end])
    if call_name(node) == "similar" && !isempty(arguments) && literal_container(first(arguments))
        return ["`similar` of the literal type `$(SYNTAX.sourcetext(first(arguments)))` inherits no array type; take the template from an input array (`similar(x, T, dims)`) or an array type argument (`similar(A, dims)`)"]
    elseif literal_container(first(parts)) && !isempty(arguments) && is_identifier(first(arguments), "undef")
        return ["`$(SYNTAX.sourcetext(first(parts)))(undef, …)` inherits no array type; build it with `similar` of an input array or an array type argument"]
    end
    return String[]
end

"""Add a site to `sites` for each literal-container array construction below syntax `node` of `source`."""
function literal_array_sites!(sites::AbstractVector{Site}, source::Source, node::SYNTAX.SyntaxNode)::Nothing
    if SYNTAX.kind(node) === CALL_KIND
        for detail in literal_array_detail(node)
            push!(sites, Site(source.name, source.path, first(SYNTAX.source_location(node)), detail))
        end
    end
    for child in node_children(node)
        literal_array_sites!(sites, source, child)
    end
    return nothing
end

"""The `literal-array` sites of the Julia file `source`."""
function literal_array_sites(source::Source)::Vector{Site}
    sites = Site[]
    literal_array_sites!(sites, source, source.tree)
    return sites
end

"""
    type_disruption_sites!(context)

The sites of each sub-check of `type-disruption`, by sub-check name. `float-widening` reads the entry
frames in `context`; with none it finds nothing.
"""
function type_disruption_sites!(context::Context)::Dict{String, Vector{Site}}
    widening = Site[]
    if !isempty(context.inferred)
        widening = float_widenings(context.repository, context.inferred; search = context.candidates, context.comments)
    end
    return Dict{String, Vector{Site}}(
        "float-widening" => widening,
        "float64" => collect(Site, Iterators.flatten(float64_sites.(context.sources))),
        "literal-array" => collect(Site, Iterators.flatten(literal_array_sites.(context.sources))),
    )
end

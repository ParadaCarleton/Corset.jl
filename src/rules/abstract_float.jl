# The rule `abstract-float`: an annotation or type bound that names `AbstractFloat` shuts out the other reals
# (`Rational`, intervals, fixed-point, dual numbers, units); `Real` accepts them. A method whose body needs
# float-only operations keeps `AbstractFloat`, because there it is the true requirement.

# Operations only floating-point numbers support, so a method that calls one needs `AbstractFloat`.
const FLOAT_ONLY_NAMES = ("eps", "nextfloat", "prevfloat", "floatmax", "floatmin", "significand", "exponent", "maxintfloat", "issubnormal")

# The integer types a `reinterpret` of a float bit pattern targets.
const BIT_PATTERN_TYPE = r"^U?Int(8|16|32|64|128)?$"

# Syntax parents whose `T <: Bound` is a type bound; elsewhere `<:` is a comparison or a struct's supertype.
const BOUND_PARENT_KINDS = (CURLY_KIND, SYNTAX.@K_str("braces"), SYNTAX.@K_str("where"))
const ASSERT_KIND = SYNTAX.@K_str "::"

"""One `AbstractFloat` in a type position: its identifier `node`, and the `owner` method name (`""` outside a method)."""
struct FloatAnnotation
    node::SYNTAX.SyntaxNode
    owner::String
end

"""The method name syntax `node` defines (`""` for any other node): a `function` block or a short-form `f(…) = …`, below any `where` or result annotation."""
function definition_name(node::SYNTAX.SyntaxNode)::String
    if SYNTAX.kind(node) ∉ (SYNTAX.@K_str("function"), KEYWORD_KIND) || isempty(node_children(node))
        return ""
    end
    signature = first(node_children(node))
    while SYNTAX.kind(signature) in (SYNTAX.@K_str("where"), ASSERT_KIND)
        signature = first(node_children(signature))
    end
    return SYNTAX.kind(signature) === CALL_KIND ? SYNTAX.sourcetext(first(node_children(signature))) : ""
end

"""Whether syntax `node` is a `reinterpret` into an integer type, which reads a float's bit pattern."""
function reads_bit_pattern(node::SYNTAX.SyntaxNode)::Bool
    parts = node_children(node)
    return SYNTAX.kind(node) === CALL_KIND && length(parts) > 1 && is_identifier(first(parts), "reinterpret") && occursin(BIT_PATTERN_TYPE, SYNTAX.sourcetext(parts[2]))
end

"""Whether syntax `node` or anything below it needs a float: a float-only operation (`FLOAT_ONLY_NAMES`) or a `reinterpret` into an integer."""
function needs_float(node::SYNTAX.SyntaxNode)::Bool
    if SYNTAX.kind(node) === IDENTIFIER_KIND && SYNTAX.sourcetext(node) in FLOAT_ONLY_NAMES
        return true
    end
    return reads_bit_pattern(node) || any(needs_float, node_children(node))
end

"""
The `AbstractFloat`s in a type position at or below syntax `node`: the type of `x::T` or `::T`, the bound of `T <: B`
under a `where`, braces or curly, and anything inside those. `typed` is whether `node` already sits in one, and
`exempt` whether the method around it needs a float.
"""
function float_annotations(node::SYNTAX.SyntaxNode, typed::Bool, exempt::Bool, owner::String)::Vector{FloatAnnotation}
    kind = SYNTAX.kind(node)
    if kind === IDENTIFIER_KIND
        return typed && !exempt && SYNTAX.sourcetext(node) == "AbstractFloat" ? [FloatAnnotation(node, owner)] : FloatAnnotation[]
    end
    name = definition_name(node)
    inner_owner = isempty(name) ? owner : name
    inner_exempt = exempt || (!isempty(name) && needs_float(node))
    parts = node_children(node)
    bound = !isnothing(node.parent) && SYNTAX.kind(node.parent) in BOUND_PARENT_KINDS
    found = FloatAnnotation[]
    for (position, part) in enumerate(parts)
        annotated = typed || (position == length(parts) && (kind === ASSERT_KIND || (kind === SUBTYPE_KIND && bound)))
        append!(found, float_annotations(part, annotated, inner_exempt, inner_owner))
    end
    return found
end

"""The sites of the Julia file `source` that annotate `AbstractFloat` where `Real` would do, one per mention."""
function abstract_floats(source::Source)::Vector{Site}
    (; path, name, tree) = source
    return [
        Site(name, path, first(SYNTAX.source_location(use.node)), "`AbstractFloat` shuts out rationals, intervals, dual numbers and units; write `Real`")
            for use in float_annotations(tree, false, false, "")
    ]
end

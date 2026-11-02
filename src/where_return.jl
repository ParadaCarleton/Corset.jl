# Short-form definitions `f(x)::R where {E} = body`, which parse as `f(x)::(R where {E})`: the
# `where` binds the return annotation, so a variable of the arguments is unbound there.

"""Whether syntax `node` is a short-form method definition `call::(R where …) = body`."""
function is_where_return(node::SYNTAX.SyntaxNode)::Bool
    if SYNTAX.kind(node) !== SYNTAX.@K_str("function") || !SYNTAX.has_flags(node, SYNTAX.SHORT_FORM_FUNCTION_FLAG)
        return false
    end
    signature = first(SYNTAX.children(node))
    parts = SYNTAX.children(signature)
    return SYNTAX.kind(signature) === SYNTAX.@K_str("::") && length(parts) == 2 &&
        SYNTAX.kind(first(parts)) === SYNTAX.@K_str("call") && SYNTAX.kind(last(parts)) === SYNTAX.@K_str("where")
end

"""The text of every identifier leaf under syntax `node`."""
function identifier_names(node::SYNTAX.SyntaxNode)::Vector{String}
    if SYNTAX.is_leaf(node)
        if SYNTAX.kind(node) === IDENTIFIER_KIND
            return [SYNTAX.sourcetext(node)]
        end
        return String[]
    end
    return reduce(vcat, [identifier_names(child) for child in SYNTAX.children(node)]; init = String[])
end

"""The variable names `where` clause `clause` introduces: `T`, `T<:B` or `{T, S<:B}`, each the first identifier of its entry."""
function introduced_names(clause::SYNTAX.SyntaxNode)::Vector{String}
    if SYNTAX.kind(clause) === SYNTAX.@K_str("braces")
        return [first(identifier_names(variable)) for variable in SYNTAX.children(clause)]
    end
    return [first(identifier_names(clause))]
end

"""Whether a variable the `where` clause of `signature` introduces occurs in the arguments of its call."""
function binds_an_argument(signature::SYNTAX.SyntaxNode)::Bool
    call, annotation = SYNTAX.children(signature)
    return !isdisjoint(introduced_names(SYNTAX.children(annotation)[2]), identifier_names(call))
end

"""Every short-form definition under syntax `node` whose `where` binds the return annotation, in source order."""
function where_return_nodes(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    if SYNTAX.is_leaf(node)
        return SYNTAX.SyntaxNode[]
    end
    below = SYNTAX.SyntaxNode[found for child in SYNTAX.children(node) for found in where_return_nodes(child)]
    if is_where_return(node)
        return vcat([node], below)
    end
    return below
end

"""The site of where-return definition `node` in `source`, at its first line."""
where_site(source::Source, node::SYNTAX.SyntaxNode)::Site = Site(source.name, source.path, first(SYNTAX.source_location(node)), "")

"""The short-form definitions of the Julia file `source` whose `where` binds the return annotation, keyed by file."""
where_return_sites(source::Source)::Vector{Site} = where_site.((source,), where_return_nodes(source.tree))

"""The parentheses that make a short-form definition of the file `path` read `(call::R) where {…}`: bytes `opening` and `closing` get one each."""
struct WhereParentheses
    path::String
    opening::Int
    closing::Int
end

"""The repair of where-return definition `node` in `source`: a `(` before its signature and a `)` after its return annotation."""
function where_repair(source::Source, node::SYNTAX.SyntaxNode)::Repair{WhereParentheses}
    signature = first(SYNTAX.children(node))
    annotation = first(SYNTAX.children(last(SYNTAX.children(signature))))
    return Repair(where_site(source, node), WhereParentheses(source.path, first(SYNTAX.byte_range(signature)), last(SYNTAX.byte_range(annotation)) + 1))
end

"""Whether the `where` of where-return definition `node` binds a variable of its arguments, so the method needs it."""
binds_its_arguments(node::SYNTAX.SyntaxNode)::Bool = binds_an_argument(first(SYNTAX.children(node)))

"""The repairs of the Julia file `source`: one per where-return definition whose `where` binds an argument."""
where_repairs(source::Source)::Vector{Repair{WhereParentheses}} = where_repair.((source,), filter(binds_its_arguments, where_return_nodes(source.tree)))

"""The text `text` with a `(` at byte `opening` and a `)` at byte `closing` of each of `edits`."""
function parenthesized(text::AbstractString, edits::AbstractVector{WhereParentheses})::String
    insertions = vcat([edit.opening => "(" for edit in edits], [edit.closing => ")" for edit in edits])
    rewritten = String(text)
    for (position, inserted) in sort(insertions; by = first, rev = true)
        rewritten = splice_text(rewritten, position:(position - 1), inserted)
    end
    return rewritten
end

"""The new text of each file `edits` touch, as path => text."""
function parenthesized_texts(edits::AbstractVector{WhereParentheses})::Vector{Pair{String, String}}
    paths = unique(String[edit.path for edit in edits])
    owners = String[edit.path for edit in edits]
    return [path => parenthesized(read(path, String), edits[owners .== path]) for path in paths]
end

"""
    where_plan(repository, directories)

The `FixPlan` that writes every short-form `f(x)::R where {E} = …` of `directories` that uses `E` in its
arguments as `(f(x)::R) where {E} = …`, the reading the long form `function f(x)::R where {E}` already has.
"""
where_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{WhereParentheses, typeof(parenthesized_texts)} =
    FixPlan(reduce(vcat, where_repairs.(directory_sources(repository, directories)); init = Repair{WhereParentheses}[]), parenthesized_texts)

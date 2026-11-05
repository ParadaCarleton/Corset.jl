# The fixer of `quadratic-vcat`: `reduce(vcat, pieces; init = T[])` becomes
# `collect(T, Iterators.flatten(pieces))`, which builds the result once.

const CALL_KIND = SYNTAX.@K_str "call"
const KEYWORD_KIND = SYNTAX.@K_str "="
const PARAMETERS_KIND = SYNTAX.@K_str "parameters"
const REF_KIND = SYNTAX.@K_str "ref"

"""A rewrite of the file `path`: its bytes `range` replaced by `text`."""
struct ByteRewrite
    path::String
    range::UnitRange{Int}
    text::String
end

"""Whether syntax `node` is the identifier `name`."""
is_identifier(node::SYNTAX.SyntaxNode, name::AbstractString)::Bool =
    SYNTAX.kind(node) === IDENTIFIER_KIND && SYNTAX.sourcetext(node) == name

"""Whether syntax `node`, an argument of a call, passes a keyword: `name = value`, or the keywords after `;`."""
keyword_part(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) in (KEYWORD_KIND, PARAMETERS_KIND)

"""The `name = value` keyword arguments of call `node`, before `;` or after it."""
keyword_arguments(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode} = SYNTAX.SyntaxNode[
    argument
        for child in node_children(node)[2:end]
        for argument in (SYNTAX.kind(child) === PARAMETERS_KIND ? node_children(child) : [child])
        if SYNTAX.kind(argument) === KEYWORD_KIND
]

"""
The element type `T` of keyword argument `init = T[]`, as syntax; `init` names no empty vector of a
type other than `Any` when the result has no children.
"""
function init_type(keyword::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    name, value = node_children(keyword)
    if !is_identifier(name, "init") || SYNTAX.kind(value) !== REF_KIND || length(node_children(value)) != 1
        return SYNTAX.SyntaxNode[]
    end
    element = only(node_children(value))
    return is_identifier(element, "Any") ? SYNTAX.SyntaxNode[] : SYNTAX.SyntaxNode[element]
end

"""
Whether syntax `node` is `reduce(vcat, pieces; init = T[])` with `T` other than `Any`. When every
piece is a vector, `collect(T, Iterators.flatten(pieces))` gives the same result in one allocation.
A piece that is not one is appended whole by `vcat` but iterated by `flatten`, which then fails to
convert to `T`, unless `T` is `Any`: the fixer leaves those folds alone.
"""
function flattenable(node::SYNTAX.SyntaxNode)::Bool
    if SYNTAX.kind(node) !== CALL_KIND
        return false
    end
    children = node_children(node)
    positional = filter(!keyword_part, children[2:end])
    keywords = keyword_arguments(node)
    return is_identifier(first(children), "reduce") && length(positional) == 2 && is_identifier(first(positional), "vcat") &&
        length(keywords) == 1 && !isempty(init_type(only(keywords)))
end

"""The outermost flattenable folds under syntax `node`, `node` itself included, in source order."""
function outer_folds(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    if flattenable(node)
        return SYNTAX.SyntaxNode[node]
    end
    return SYNTAX.SyntaxNode[found for child in node_children(node) for found in outer_folds(child)]
end

"""The text of syntax `node` of `source` with every flattenable fold inside it rewritten (`flattened_fold`)."""
function flattened_text(source::Source, node::SYNTAX.SyntaxNode)::String
    range = SYNTAX.byte_range(node)
    rewritten = String(codeunits(source.text)[range])
    for fold in reverse(SYNTAX.SyntaxNode[found for child in node_children(node) for found in outer_folds(child)])
        inner = SYNTAX.byte_range(fold) .- (first(range) - 1)
        rewritten = splice_text(rewritten, inner, flattened_fold(source, fold))
    end
    return rewritten
end

"""The text that replaces flattenable fold `node` of `source`: `collect(T, Iterators.flatten(pieces))`, its pieces flattened too."""
function flattened_fold(source::Source, node::SYNTAX.SyntaxNode)::String
    pieces = last(filter(!keyword_part, node_children(node)[2:end]))
    element = only(init_type(only(keyword_arguments(node))))
    return string("collect(", SYNTAX.sourcetext(element), ", Iterators.flatten(", flattened_text(source, pieces), "))")
end

"""The repair of flattenable fold `node` in `source`, at the lines it spans."""
function flatten_repair(source::Source, node::SYNTAX.SyntaxNode)::Repair{ByteRewrite}
    range = SYNTAX.byte_range(node)
    first_line = first(SYNTAX.source_location(node))
    last_line = first(SYNTAX.source_location(node.source, last(range)))
    site = Site(source.name, source.path, first_line, last_line, "")
    return Repair(site, ByteRewrite(source.path, range, flattened_fold(source, node)))
end

"""The repairs of the Julia file `source`: one per outermost flattenable fold, whose rewrite also flattens the folds inside it."""
flatten_repairs(source::Source)::Vector{Repair{ByteRewrite}} = flatten_repair.((source,), outer_folds(source.tree))

"""The text `text` with the `range` of each of `edits` replaced by its `text`; the ranges do not overlap."""
function rewritten(text::AbstractString, edits::AbstractVector{ByteRewrite})::String
    result = String(text)
    for edit in sort(edits; by = edit -> first(edit.range), rev = true)
        result = splice_text(result, edit.range, edit.text)
    end
    return result
end

"""The file `path` => its new text after the `edits` whose `owners` (their paths) name it."""
rewritten_file(edits::AbstractVector{ByteRewrite}, owners::AbstractVector{String}, path::String)::Pair{String, String} =
    path => rewritten(read(path, String), edits[owners .== path])

"""The new text of each file `edits` touch, as path => text."""
function rewritten_texts(edits::AbstractVector{ByteRewrite})::Vector{Pair{String, String}}
    owners = String[edit.path for edit in edits]
    return rewritten_file.((edits,), (owners,), unique(owners))
end

"""
    flatten_plan(repository, directories)

The `FixPlan` that writes every `reduce(vcat, pieces; init = T[])` of `directories`, `T` other than `Any`,
as `collect(T, Iterators.flatten(pieces))`.
"""
flatten_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)} =
    FixPlan(collect(Repair{ByteRewrite}, Iterators.flatten(flatten_repairs.(directory_sources(repository, directories)))), rewritten_texts)

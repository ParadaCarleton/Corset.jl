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

"""Whether a variable the `where` clause of `signature` introduces occurs in the arguments of its call."""
function binds_an_argument(signature::SYNTAX.SyntaxNode)::Bool
    call, annotation = SYNTAX.children(signature)
    clause = SYNTAX.children(annotation)[2]
    children = SYNTAX.children(clause)
    introduced = if isnothing(children)
        identifier_names(clause)
    else
        [first(identifier_names(variable)) for variable in children]
    end
    return !isdisjoint(introduced, identifier_names(call))
end

"""
    where_return_sites!(sites, source, node)

Push a `Site` for each short-form definition under `node` whose `where` binds the return annotation.
"""
function where_return_sites!(sites::AbstractVector{Site}, source::Source, node::SYNTAX.SyntaxNode)::Nothing
    if is_where_return(node)
        push!(sites, Site(source.name, source.path, first(SYNTAX.source_location(node)), ""))
    end
    if !SYNTAX.is_leaf(node)
        for child in SYNTAX.children(node)
            where_return_sites!(sites, source, child)
        end
    end
    return nothing
end

"""The short-form definitions of the Julia file `source` whose `where` binds the return annotation, keyed by file."""
function where_return_sites(source::Source)::Vector{Site}
    sites = Site[]
    where_return_sites!(sites, source, source.tree)
    return sites
end

"""The byte insertions (position => text) that parenthesize the signatures under `node` as `(call::R) where {…}`."""
function where_return_insertions!(insertions::AbstractVector{Pair{Int, String}}, node::SYNTAX.SyntaxNode)::Nothing
    if is_where_return(node)
        signature = first(SYNTAX.children(node))
        if binds_an_argument(signature)
            annotation = last(SYNTAX.children(signature))
            push!(insertions, first(SYNTAX.byte_range(signature)) => "(", last(SYNTAX.byte_range(first(SYNTAX.children(annotation)))) + 1 => ")")
        end
    end
    if !SYNTAX.is_leaf(node)
        for child in SYNTAX.children(node)
            where_return_insertions!(insertions, child)
        end
    end
    return nothing
end

"""
    fix_where_returns(text)

`text` with every short-form `f(x)::R where {E} = …` that uses `E` in its arguments written
`(f(x)::R) where {E} = …`, the reading the long form `function f(x)::R where {E}` already has.
"""
function fix_where_returns(text::AbstractString)::String
    insertions = Pair{Int, String}[]
    where_return_insertions!(insertions, SYNTAX.parseall(SYNTAX.SyntaxNode, text))
    bytes::Vector{UInt8} = Vector{UInt8}(codeunits(text))
    for (position, inserted) in sort(insertions; by = first, rev = true)
        bytes = vcat(bytes[1:(position - 1)], codeunits(inserted), bytes[position:end])
    end
    return String(bytes)
end

"""
    fix_where_returns!(repository, directories)

Rewrite the Julia files of `directories` with `fix_where_returns`. Returns the sites it fixed.
"""
function fix_where_returns!(repository::Repository, directories::Tuple{Vararg{String}})::Vector{Site}
    sites = Site[]
    for path in repository_sources(repository, directories)
        found = where_return_sites(Source(repository, path))
        if !isempty(found)
            write(path, fix_where_returns(read(path, String)))
            append!(sites, found)
        end
    end
    return sites
end

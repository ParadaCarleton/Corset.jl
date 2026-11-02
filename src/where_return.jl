# Short-form definitions `f(x)::R where {E} = body`, which parse as `f(x)::(R where {E})`: the
# `where` binds the return annotation, so a variable of the arguments is unbound there.

# The rule's name in opt-out comments, as `registry.jl` registers it.
const WHERE_RETURN_RULE = "where-return"

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

"""
    where_return_sites!(sites, path, node)

Push a `Site` for each short-form definition under `node` whose `where` binds the return annotation.
"""
function where_return_sites!(sites::AbstractVector{Site}, path::AbstractString, node::SYNTAX.SyntaxNode)::Nothing
    if is_where_return(node)
        push!(sites, Site(basename(path), path, first(SYNTAX.source_location(node)), ""))
    end
    if !SYNTAX.is_leaf(node)
        for child in SYNTAX.children(node)
            where_return_sites!(sites, path, child)
        end
    end
    return nothing
end

"""The short-form definitions of the Julia file `path` whose `where` binds the return annotation, keyed by file."""
function where_return_sites(path::AbstractString)::Vector{Site}
    sites = Site[]
    where_return_sites!(sites, path, SYNTAX.parseall(SYNTAX.SyntaxNode, read(path, String)))
    return sites
end

"""
The byte insertions (position => text) that parenthesize the signatures under `node` as `(call::R) where {…}`,
except at a definition whose first line `skipped` opts out.
"""
function where_return_insertions!(insertions::AbstractVector{Pair{Int, String}}, node::SYNTAX.SyntaxNode, skipped::OptOuts)::Nothing
    if is_where_return(node) && !covers(skipped, first(SYNTAX.source_location(node)))
        signature = first(SYNTAX.children(node))
        if binds_an_argument(signature)
            annotation = last(SYNTAX.children(signature))
            push!(insertions, first(SYNTAX.byte_range(signature)) => "(", last(SYNTAX.byte_range(first(SYNTAX.children(annotation)))) + 1 => ")")
        end
    end
    if !SYNTAX.is_leaf(node)
        for child in SYNTAX.children(node)
            where_return_insertions!(insertions, child, skipped)
        end
    end
    return nothing
end

"""
    fix_where_returns(path)

The text of the Julia file `path` with every short-form `f(x)::R where {E} = …` that uses `E` in its
arguments written `(f(x)::R) where {E} = …`, the reading the long form `function f(x)::R where {E}`
already has. A definition a `# lint: where-return` comment opts out stays.
"""
function fix_where_returns(path::AbstractString)::String
    text = read(path, String)
    insertions = Pair{Int, String}[]
    where_return_insertions!(insertions, SYNTAX.parseall(SYNTAX.SyntaxNode, text), opt_outs(path, WHERE_RETURN_RULE))
    bytes::Vector{UInt8} = Vector{UInt8}(codeunits(text))
    for (position, inserted) in sort(insertions; by = first, rev = true)
        bytes = vcat(bytes[1:(position - 1)], codeunits(inserted), bytes[position:end])
    end
    return String(bytes)
end

"""
    fix_where_returns!(repository, directories)

Rewrite the Julia files of `directories` with `fix_where_returns`. Returns the sites it fixed: those
no `# lint: where-return` comment opts out.
"""
function fix_where_returns!(repository::Repository, directories::Tuple{Vararg{String}})::Vector{Site}
    sites = Site[]
    for path in repository_sources(repository, directories)
        found, _ = unopted(where_return_sites(path), WHERE_RETURN_RULE)
        if !isempty(found)
            write(path, fix_where_returns(path))
            append!(sites, found)
        end
    end
    return sites
end

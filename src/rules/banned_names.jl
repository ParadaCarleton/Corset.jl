# The `banned-name` rule: names a project forbids, by word or suffix (`Repository.banned_words`, `banned_suffixes`).

"""Whether `name` holds a banned word (one of its `_`-separated words, any case) or ends in a banned suffix."""
function is_banned(name::Symbol, words::Tuple{Vararg{String}}, suffixes::Tuple{Vararg{String}})::Bool
    text = lowercase(string(name))
    return any(in(words), split(text, '_'; keepempty = false)) || any(suffix -> endswith(text, suffix), suffixes)
end

"""The names parsed expression `node` declares: its `binding_names`, a function's own name, and a struct's field names."""
function declared_names(node::Expr)::Vector{Symbol}
    names = binding_names(node)
    call = signature_call(node)
    if !isnothing(call) && first(call.args) isa Symbol
        push!(names, first(call.args))
    end
    if node.head === :struct
        append!(names, Iterators.flatten(bound_names.(filter(field -> Meta.isexpr(field, :(::)), last(node.args).args))))
    end
    return names
end

"""One site per banned name declared in `source`, keyed by file and enclosing function, at the declaring line."""
function banned_name_sites(repository::Repository, source::Source)::Vector{Site}
    (; banned_words, banned_suffixes) = repository
    return [
        Site("$(source.name) $(item.enclosing)", source.path, item.line, "`$name` is a banned name; pick a descriptive one")
            for item in source.located
            for name in declared_names(item.node) if is_banned(name, banned_words, banned_suffixes)
    ]
end

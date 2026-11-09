# The `banned-name` rule: names a project forbids, by word or suffix (`Repository.banned_words`, `banned_suffixes`).

"""Whether `name` holds a word `repository` bans (one of its `_`-separated words, any case) or ends in a suffix it bans."""
function is_banned(name::Symbol, repository::Repository)::Bool
    text = lowercase(string(name))
    for word in split(text, '_'; keepempty = false)
        for banned in repository.banned_words
            if word == banned
                return true
            end
        end
    end
    for suffix in repository.banned_suffixes
        if endswith(text, suffix)
            return true
        end
    end
    return false
end

"""The names parsed expression `node` declares: its `binding_names`, a function's own name, and a struct's field names."""
function declared_names(node::Expr)::Vector{Symbol}
    names = binding_names(node)
    call = signature_call(node)
    if !isnothing(call) && first(call.args) isa Symbol
        push!(names, first(call.args)::Symbol)
    end
    if node.head === :struct && last(node.args) isa Expr
        for name in Iterators.flatten(declared_fields.((last(node.args)::Expr).args))
            push!(names, name)
        end
    end
    return names
end

"""The names a struct body member `field` declares: those of a `name::Type` field, none for a constructor or a line marker."""
declared_fields(field::Expr)::Vector{Symbol} = field.head === :(::) ? bound_names(field) : Symbol[]
declared_fields(::Any)::Vector{Symbol} = Symbol[]

"""One site per banned name declared in `source`, keyed by file and enclosing function, at the declaring line."""
function banned_name_sites(repository::Repository, source::Source)::Vector{Site}
    sites = Site[]
    for item in source.located
        for name in declared_names(item.node)
            if is_banned(name, repository)
                push!(sites, Site("$(source.name) $(item.enclosing)", source.path, item.line, "`$name` is a banned name; pick a descriptive one"))
            end
        end
    end
    return sites
end

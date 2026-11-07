# Rules on argument annotations that accept less than they mean to. `enumerated-union`: a `Union`
# that lists concrete types (`Union{Float32, Float64}`) where their common supertype (`AbstractFloat`)
# says what the method takes. `invariant-parameter`: an abstract type parameter written without `<:`
# (`AbstractVector{Real}`), which a container of a concrete subtype (`Vector{Float64}`) does not match.
#
# The rules read parsed annotations and resolve their names by reflection, so the values they handle
# have no static type: the helpers below opt out of the rules on inferred code that flag that.

# lint: runtime-dispatch-begin  parsed `Expr` arguments and the types reflection returns have no static type
# lint: unmarked-mutation-begin  only reads parsed annotations; the possible writes are the runtime dispatches

"""A type expression `resolved_type` cannot resolve without running code, or one naming a type variable."""
struct Unresolved end

"""
    resolved_type(annotation, scope, variables = ())

The value parsed type expression `annotation` names in `scope`: a type, or a parameter value (`2` of
`Array{Float64, 2}`). Names, qualified names (`LinearAlgebra.BlasFloat`), parameterized types of
those and literals resolve; anything else, a name `scope` does not bind and one of the type
`variables` give `Unresolved()`. No call is run.
"""
function resolved_type(annotation::Symbol, scope::Module, variables::Any = ())::Any # lint: widened-return # lint: abstract-local  a name may bind any value
    if annotation in variables || !isdefined(scope, annotation)
        return Unresolved()
    end
    return getglobal(scope, annotation)
end
function resolved_type(annotation::Expr, scope::Module, variables::Any = ())::Any # lint: widened-return # lint: abstract-local  Expr nodes hold untyped arguments
    if annotation.head === :. && length(annotation.args) == 2 && last(annotation.args) isa QuoteNode
        owner = resolved_type(first(annotation.args), scope, variables)
        name = last(annotation.args).value
        if owner isa Module && name isa Symbol && isdefined(owner, name)
            return getglobal(owner, name)
        end
    elseif annotation.head === :curly
        parts = resolved_type.(annotation.args, (scope,), (variables,))
        if !any(Base.Fix2(isa, Unresolved), parts)
            return applied_type(first(parts), parts[2:end])
        end
    end
    return Unresolved()
end
resolved_type(annotation::QuoteNode, ::Module, ::Any = ())::Any = annotation.value # lint: widened-return  a quoted parameter may be any value
(resolved_type(annotation::T, ::Module, ::Any = ())::T) where {T <: Union{Integer, Char}} = annotation
resolved_type(::Any, ::Module, ::Any = ())::Unresolved = Unresolved()

"""`head{parameters...}`, or `Unresolved()` when `head` takes no such parameters (a name `scope` binds to something else)."""
function applied_type(head::Any, parameters::AbstractVector)::Any # lint: widened-return # lint: abstract-local  reflects on values of unknown type
    try
        return head{parameters...}
    catch failure
        if failure isa TypeError || failure isa ErrorException
            return Unresolved()
        end
        rethrow() # COV_EXCL_LINE
    end
end

"""Every parsed `{}` expression below type expression `annotation`, `annotation` first: `Union{…}` and `Vector{…}` alike."""
function curly_expressions(annotation::Expr)::Vector{Expr} # lint: abstract-local  Expr nodes hold untyped arguments
    found = annotation.head === :curly ? Expr[annotation] : Expr[]
    for argument in annotation.args
        append!(found, curly_expressions(argument))
    end
    return found
end
curly_expressions(::Any)::Vector{Expr} = Expr[]

"""The annotations of method definition `node` a caller's argument must match: each argument's, and each `where` bound's (`AbstractVector{Real}` of `V <: AbstractVector{Real}`)."""
function argument_annotations(node::Expr)::Vector{Any} # lint: abstract-local  Expr nodes hold untyped arguments
    annotations = Any[]
    for argument in signature_call(node).args[2:end]
        append!(annotations, last.(annotated_arguments(argument)))
    end
    signature = node.args[1]
    while signature isa Expr && signature.head in (:where, :(::))
        if signature.head === :where
            for entry in signature.args[2:end]
                if Meta.isexpr(entry, :<:, 2)
                    push!(annotations, last(entry.args))
                end
            end
        end
        signature = signature.args[1]
    end
    return annotations
end

"""Whether `type` is a type of `scope`'s package, which the package lists in a union by choice (its own exceptions); never so for Base or Core."""
own_type(type::Type, scope::Module)::Bool = !(scope in (Base, Core)) && type isa DataType && within(parentmodule(type), scope)

"""
    enumerated_supertype(node, scope, variables = ())

The common supertype of the types parsed `Union{…}` expression `node` lists in `scope`
(`AbstractFloat` of `Union{Float32, Float64}`) when it lists two or more concrete types besides
`Nothing` and `Missing`, none of them the package's own (`own_type`); otherwise `Any`, as for members
that share only `Any`. A member that names a type variable or does not resolve gives `Any` too.
"""
function enumerated_supertype(node::Expr, scope::Module, variables::Any = ())::Type # lint: widened-return # lint: abstract-local  reflects on the types the members name
    members = resolved_type.(node.args[2:end], (scope,), (variables,))
    if !all(Base.Fix2(isa, Type), members)
        return Any
    end
    listed = collect(Type, filter(!absent_value, members))
    if length(listed) < 2 || !all(isconcretetype, listed) || any(Base.Fix2(own_type, scope), listed)
        return Any
    end
    return reduce(typejoin, listed)
end

"""The repair text of an enumerated union `node` whose members share `supertype`; its `Nothing` and `Missing` members stay in the repair."""
function enumerated_detail(node::Expr, supertype::Type)::String # lint: abstract-local  Expr nodes hold untyped arguments
    absent = [string(member) for member in node.args[2:end] if member in (:Nothing, :Missing)]
    repair = isempty(absent) ? string(supertype) : "Union{$(join([absent; string(supertype)], ", "))}"
    return "`$node` lists subtypes of `$supertype`: take `$repair`, or add a method that takes the rest beside this one"
end

"""Whether `method` was compiled from the definition at `place`: its lines and the path of its file."""
defined_at(method::Method, place::Tuple{UnitRange{Int}, String})::Bool =
    method.line in first(place) && isfile(string(method.file)) && samefile(string(method.file), last(place))

"""Whether `other` is a method beside `method` whose signature takes all of `method`'s arguments."""
covers(other::Method, method::Method)::Bool = other !== method && method.sig <: other.sig

"""Whether one of `siblings` `covers` `method`."""
covered(method::Method, siblings::AbstractVector{Method})::Bool = any(Base.Fix2(covers, method), siblings)

"""
    covered_by_sibling(item, source, scope)

Whether every method `scope` compiled from definition `item` of `source` has a sibling method of the
same function whose signature takes all its arguments: the generic fallback beside a specialized
method (`f(x::Union{Float32, Float64})` beside `f(x::Real)`). A function `scope` does not bind
has no sibling it can see.
"""
function covered_by_sibling(item::Located, source::Source, scope::Module)::Bool
    name = defined_name(item.node)
    if isnothing(name) || !isdefined(scope, name)
        return false
    end
    siblings = collect(Method, methods(getglobal(scope, name)))
    own = filter(Base.Fix2(defined_at, (definition_lines(item.node, item.line), source.path)), siblings)
    return !isempty(own) && all(Base.Fix2(covered, siblings), own)
end

"""The sites of the `unions` whose entry of `supertypes` is narrower than `Any`, keyed `key` and placed at `lines` of `path`."""
function union_sites(unions::AbstractVector{Expr}, supertypes::AbstractVector{<:Type}, key::String, path::String, lines::UnitRange{Int})::Vector{Site}
    sites = Site[]
    for (node, supertype) in zip(unions, supertypes)
        if supertype !== Any
            push!(sites, Site(key, path, first(lines), last(lines), enumerated_detail(node, supertype)))
        end
    end
    return sites
end

"""Whether parsed `{}` expression `node` is a `Union{…}`."""
is_union(node::Expr)::Bool = first(node.args) === :Union

"""
    enumerated_unions(source, scope)

Each `Union` of two or more concrete types besides `Nothing` and `Missing` that share a supertype
narrower than `Any` (`enumerated_supertype`), in an argument annotation, a `where` bound or a `const`
alias of `source`, its names resolved in `scope`: `Union{Float32, Float64}` turns away `Float16`,
`BigFloat` and the dual numbers of automatic differentiation, which `AbstractFloat` takes. One site
per union, keyed by file and the defined name. A method with a sibling that takes all its
arguments (`covered_by_sibling`) is exempt: the union picks a fast path, as with BLAS's float types.
"""
function enumerated_unions(source::Source, scope::Module)::Vector{Site} # lint: abstract-local  Expr nodes hold untyped arguments
    sites = Site[]
    for item in source.located
        if !isnothing(signature_call(item.node)) && length(item.node.args) >= 2
            unions = filter(is_union, collect(Expr, Iterators.flatten(curly_expressions.(argument_annotations(item.node)))))
            supertypes = collect(Type, enumerated_supertype.(unions, (scope,), (where_variables(item.node),)))
            if !all(Base.Fix1(===, Any), supertypes) && !covered_by_sibling(item, source, scope)
                key = "$(source.name) $(defined_name(item.node))"
                append!(sites, union_sites(unions, supertypes, key, source.path, definition_lines(item.node, item.line)))
            end
        elseif item.node.head === :const && Meta.isexpr(only(item.node.args), :(=), 2)
            alias, value = only(item.node.args).args
            aliased = filter(is_union, curly_expressions(value))
            alias_supertypes = collect(Type, enumerated_supertype.(aliased, (scope,), (Meta.isexpr(alias, :curly) ? alias.args[2:end] : (),)))
            append!(sites, union_sites(aliased, alias_supertypes, "$(source.name) $(type_head(alias))", source.path, item.line:item.line))
        end
    end
    return sites
end

# Heads whose parameters are covariant (`Tuple{Float64} <: Tuple{Real}`) or stand for themselves
# (`Type{Real}` is the type `Real`, `Val{1}` the value 1): an abstract parameter there matches its subtypes.
const COVARIANT_HEADS = (:Tuple, :NTuple, :Vararg, :Type, :Val, :Union)

"""
    invariant_parameter(node, index, scope, variables = ())

Whether parameter `index` of parsed `{}` expression `node` is an abstract type written without `<:`
(`Real` of `AbstractVector{Real}`), so only that exact parameter matches: `Vector{Float64}` is no
`AbstractVector{Real}`. `Any`, a type variable, a value and the parameters of `COVARIANT_HEADS` are fine.
"""
function invariant_parameter(node::Expr, index::Int, scope::Module, variables::Any = ())::Bool # lint: abstract-local  reflects on values of unknown type
    head = resolved_type(first(node.args), scope, variables)
    if type_head(node) in COVARIANT_HEADS || any(Base.Fix1(===, head), (Tuple, NTuple, Type, Val))
        return false
    end
    parameter = resolved_type(node.args[index], scope, variables)
    return parameter isa Type && parameter !== Any && parameter !== Union{} && !isconcretetype(parameter)
end

"""The `{}` expression `node` with parameter `index` written as `<:` that parameter: `AbstractVector{<:Real}`."""
function widened_parameter(node::Expr, index::Int)::Expr
    widened = copy(node)
    widened.args[index] = Expr(:<:, node.args[index])
    return widened
end

"""
    invariant_parameters(source, scope)

Each abstract type parameter written without `<:` (`invariant_parameter`) in an argument annotation or
`where` bound of `source`, its names resolved in `scope`: `f(xs::AbstractVector{Real})` throws a
`MethodError` for `f([1.0, 2.0])`, which `AbstractVector{<:Real}` takes. One site per parameter,
keyed by file and the defined name; the detail names the `<:` form.
"""
function invariant_parameters(source::Source, scope::Module)::Vector{Site} # lint: abstract-local  Expr nodes hold untyped arguments
    sites = Site[]
    for item in source.located
        if isnothing(signature_call(item.node)) || length(item.node.args) < 2
            continue
        end
        variables = where_variables(item.node)
        span = definition_lines(item.node, item.line)
        for node in collect(Expr, Iterators.flatten(curly_expressions.(argument_annotations(item.node))))
            for index in 2:length(node.args)
                if invariant_parameter(node, index, scope, variables)
                    detail = "`$node` takes only the parameter `$(node.args[index])` itself; write `$(widened_parameter(node, index))`"
                    push!(sites, Site("$(source.name) $(defined_name(item.node))", source.path, first(span), last(span), detail))
                end
            end
        end
    end
    return sites
end

# lint: unmarked-mutation-end
# lint: runtime-dispatch-end

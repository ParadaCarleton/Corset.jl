# Rules on argument annotations that accept less than they mean to. `invariant-parameter`: an
# abstract type parameter written without `<:` (`AbstractVector{Real}`), which a container of a
# concrete subtype (`Vector{Float64}`) does not match.
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

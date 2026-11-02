# Source rules on parsed expressions for error handling, path checks, scans and file writes.

"""Every expression in parsed expression `node`, `node` first."""
nested(node::Expr)::Vector{Expr} = reduce(vcat, nested.(node.args); init = [node])
nested(::Any)::Vector{Expr} = Expr[]

"""The empty name: what `called_name` and `callee` give for an expression that names no function."""
const NO_NAME = Symbol("")

"""The name a parsed callee `node` calls: `f` for `f` and `Base.f`; `NO_NAME` for anything else."""
called_name(node::Symbol)::Symbol = node
called_name(node::QuoteNode)::Symbol = called_name(node.value) # lint: runtime-dispatch # lint: unmarked-mutation  a quoted name is untyped
function called_name(node::Expr)::Symbol # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if node.head === :. && length(node.args) == 2
        return called_name(last(node.args))
    end
    return NO_NAME
end
called_name(::Any)::Symbol = NO_NAME

"""Whether parsed expression `node` is a broadcast call `f.(x)`."""
is_broadcast(node::Expr)::Bool = node.head === :. && length(node.args) == 2 && Meta.isexpr(node.args[2], :tuple)

"""The function parsed expression `node` calls, plainly (`f(x)`) or by broadcast (`f.(x)`); `NO_NAME` when it calls none."""
function callee(node::Expr)::Symbol # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if node.head === :call || is_broadcast(node)
        return called_name(first(node.args))
    end
    return NO_NAME
end
callee(::Any)::Symbol = NO_NAME

"""The arguments of call or broadcast `node`, without the callee."""
function call_arguments(node::Expr)::AbstractVector
    if is_broadcast(node)
        return (last(node.args)::Expr).args
    end
    return node.args[2:end]
end

"""The first line marker in parsed expression `node`, or `fallback` when it has none."""
first_line(node::Expr, fallback::Integer)::Int = first([Int[argument.line for argument in node.args if argument isa LineNumberNode]; fallback])

"""The variable a parsed `try` expression `node` binds the caught exception to; `NO_NAME` when it binds none."""
function catch_binding(node::Expr)::Symbol # lint: abstract-local  Expr nodes hold untyped arguments
    binding = node.args[2]
    if binding isa Symbol
        return binding
    end
    return NO_NAME
end

"""Whether parsed expression `node` re-raises what the catch binding `caught` holds: `rethrow()`, `rethrow(caught)` or `throw(caught)`."""
reraises(node::Expr, caught::Symbol)::Bool = callee(node) === :rethrow ||
    (caught !== NO_NAME && callee(node) === :throw && length(node.args) == 2 && node.args[2] === caught)

"""Whether parsed `try` expression `node` has a `catch` block that re-raises nothing: every exception, an internal error included, ends there alike."""
is_broad_catch(node::Expr)::Bool = node.head === :try && Meta.isexpr(node.args[3], :block) &&
    !any(Base.Fix2(reraises, catch_binding(node)), nested(node.args[3]))

"""
`catch` blocks that handle every exception alike, keyed by file and the function they sit in, placed
from the `try` line to the catch block's first line. A block that calls `rethrow()`, or throws what it
caught, passes: test the type with `isa`, handle the expected ones and rethrow the rest.
"""
function broad_catches(source::Source)::Vector{Site}
    (; path, name, located) = source
    return [
        Site("$name $(item.enclosing)", path, item.line, first_line(item.node.args[3], item.line), "catches every exception alike")
            for item in located if is_broad_catch(item.node)
    ]
end

"""The functions that test whether a path exists."""
const EXISTENCE_TESTS = (:isdir, :isfile, :ispath, :isdirpath)

"""Whether parsed expression `node` is a plain call of a path test: `isfile(path)`."""
is_existence_call(node::Any)::Bool = Meta.isexpr(node, :call) && callee(node) in EXISTENCE_TESTS

"""Whether condition `node` is a path test, alone or as one operand of `&&`."""
is_existence_condition(node::Any)::Bool = is_existence_call(node) || # lint: runtime-dispatch  Expr nodes hold untyped arguments
    (Meta.isexpr(node, :&&) && any(is_existence_condition, (node::Expr).args))

"""Whether function body `node` ends in a path test: its last statement, or the body itself when it is no block."""
function returns_existence(node::Any)::Bool # lint: runtime-dispatch  Expr nodes hold untyped arguments
    if Meta.isexpr(node, :block)
        return is_existence_condition(last((node::Expr).args))
    end
    return is_existence_condition(node)
end

"""
Whether parsed function `node` keeps what exists: a path test (`isdir`, `Base.isfile`), one composed
with another function (`isdir ∘ f`), or an anonymous function whose result is one (`x -> isfile(x)`).
"""
is_existence_predicate(node::Symbol)::Bool = node in EXISTENCE_TESTS
function is_existence_predicate(node::Expr)::Bool # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if node.head === :->
        return returns_existence(node.args[2])
    end
    if node.head === :call && callee(node) === :∘
        return is_existence_predicate(node.args[2])
    end
    return node.head === :. && called_name(node) in EXISTENCE_TESTS
end
is_existence_predicate(::Any)::Bool = false

"""
Whether parsed expression `node` drops the paths that do not exist: `filter(isdir, paths)` and its
`do` form, a mask `paths[isfile.(paths)]`, or a comprehension or generator filtered by `if ispath(path)`.
"""
function drops_missing_paths(node::Expr)::Bool # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if node.head === :call && callee(node) in (:filter, :filter!)
        return length(node.args) >= 3 && is_existence_predicate(node.args[2])
    end
    if node.head === :do
        return callee(node.args[1]) in (:filter, :filter!) && is_existence_predicate(node.args[2])
    end
    if node.head === :ref
        return any(index -> Meta.isexpr(index, :.) && is_broadcast(index) && callee(index) in EXISTENCE_TESTS, node.args[2:end])
    end
    return node.head === :filter && is_existence_condition(node.args[1])
end

"""The expressions inside the arguments of call `node`."""
argument_expressions(node::Expr)::Vector{Expr} = reduce( # lint: unmarked-mutation  Expr nodes hold untyped arguments
    vcat, nested.(call_arguments(node)); init = Expr[]
)

"""The expressions inside the arguments of every `rm` call or broadcast among `located`: a cleanup removes only what exists."""
cleanup_expressions(located::AbstractVector{Located})::Vector{Expr} =
    mapreduce(argument_expressions, vcat, [item.node for item in located if callee(item.node) === :rm]; init = Expr[])

"""Whether `item` drops the paths that do not exist outside the `cleanup` expressions."""
hides_missing_paths(cleanup::AbstractVector{Expr}, item::Located)::Bool =
    drops_missing_paths(item.node) && !any(Base.Fix1(===, item.node), cleanup)

"""
Path filters that drop the paths that do not exist, keyed by file and the function they sit in. A
path the user named that is missing is a typo to report, so the filter hides it; a filter feeding `rm` passes.
"""
function silent_existence_filters(source::Source)::Vector{Site}
    (; path, name, located) = source
    return [
        Site("$name $(item.enclosing)", path, item.line, "drops the paths that do not exist")
            for item in filter(Base.Fix1(hides_missing_paths, cleanup_expressions(located)), located)
    ]
end

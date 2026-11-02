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

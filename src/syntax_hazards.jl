# Source rules on parsed expressions for error handling, path checks, scans and file writes.

"""Every expression in parsed expression `node`, `node` first."""
nested(node::Expr)::Vector{Expr} = Expr[node; collect(Expr, Iterators.flatten(nested.(node.args)))]
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

"""The positional arguments of call or broadcast `node`: neither the callee nor the keywords after `;`."""
function call_arguments(node::Expr)::AbstractVector
    if is_broadcast(node)
        return filter(!Base.Fix2(Meta.isexpr, :parameters), (last(node.args)::Expr).args)
    end
    return filter(!Base.Fix2(Meta.isexpr, :parameters), node.args[2:end])
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

"""Whether the block `body` of an anonymous function ends in a path test."""
returns_existence(body::Expr)::Bool = is_existence_condition(last(body.args)) # lint: runtime-dispatch  Expr nodes hold untyped arguments

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
argument_expressions(node::Expr)::Vector{Expr} = collect(Expr, Iterators.flatten(nested.(call_arguments(node)))) # lint: unmarked-mutation  Expr nodes hold untyped arguments

"""The expressions inside the arguments of every `rm` call or broadcast among `located`: a cleanup removes only what exists."""
cleanup_expressions(located::AbstractVector{Located})::Vector{Expr} =
    collect(Expr, Iterators.flatten(argument_expressions.([item.node for item in located if callee(item.node) === :rm])))

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

"""The calls that scan a whole collection."""
const SCANS = (:filter, :findall, :findfirst, :findlast, :count, :any, :all, :in, :∈, :∉)

"""The calls that run an anonymous function once per element of the collections after it."""
const ELEMENTWISE = (:map, :foreach, :filter, :count, :any, :all, :sum, :findall, :findfirst, :findlast)

"""The calls whose result iterates over their arguments: `enumerate(xs)` walks `xs`."""
const ITERATION_WRAPPERS = (:enumerate, :pairs, :eachindex, :zip, :keys, :values, :axes, :reverse)

"""Whether parsed expression `node` names a collection: a variable `xs` or a field `a.xs`."""
is_name(::Symbol)::Bool = true
is_name(node::Expr)::Bool = node.head === :. && length(node.args) == 2 && node.args[2] isa QuoteNode && is_name(node.args[1]) # lint: runtime-dispatch  Expr nodes hold untyped arguments
is_name(::Any)::Bool = false

"""The named collections that iterating parsed expression `node` walks: `xs` for `xs`, `enumerate(xs)` and `zip(xs, ys)` (with `ys`)."""
function iterated(node::Any)::Vector{Union{Symbol, Expr}} # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if is_name(node)
        return Union{Symbol, Expr}[node]
    end
    if Meta.isexpr(node, :call) && callee(node) in ITERATION_WRAPPERS
        return collect(Union{Symbol, Expr}, Iterators.flatten(iterated.(call_arguments(node))))
    end
    return Union{Symbol, Expr}[]
end

"""The named collections that iterating each of `nodes` walks."""
all_iterated(nodes::AbstractVector)::Vector{Union{Symbol, Expr}} = collect(Union{Symbol, Expr}, Iterators.flatten(iterated.(nodes))) # lint: runtime-dispatch  Expr nodes hold untyped arguments

"""The iteration specifications `x = xs` (how `for` and generators parse `x in xs`) in a loop `header`: one, a block of them, or a generator's `if` filter over them."""
function iteration_specs(header::Any)::Vector{Expr} # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if Meta.isexpr(header, :(=))
        return Expr[header]
    end
    if Meta.isexpr(header, :block) || Meta.isexpr(header, :filter)
        return collect(Expr, Iterators.flatten(iteration_specs.((header::Expr).args)))
    end
    return Expr[]
end

"""The named collections the loop `headers` walk."""
header_collections(headers::AbstractVector)::Vector{Union{Symbol, Expr}} = # lint: runtime-dispatch  Expr nodes hold untyped arguments
    all_iterated([last(spec.args) for spec in collect(Expr, Iterators.flatten(iteration_specs.(headers)))])

"""
The named collections parsed expression `node` walks element by element, and the expressions it
evaluates per element: a `for` loop, a generator or comprehension (its `if` conditions included), an
anonymous function passed to `map`, `count` and the like (`do` form included), or broadcast.
"""
function element_loop(node::Expr)::Tuple{Vector{Union{Symbol, Expr}}, Vector{Expr}} # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if node.head === :for
        return header_collections(node.args[1:1]), nested(node.args[2])
    end
    if node.head === :generator
        return header_collections(node.args[2:end]), [nested(node.args[1]); collect(Expr, Iterators.flatten(nested.(node.args[2:end])))]
    end
    if node.head === :do && callee(node.args[1]) in ELEMENTWISE
        return all_iterated(call_arguments(node.args[1])), nested(node.args[2])
    end
    if node.head === :call && callee(node) in ELEMENTWISE && Meta.isexpr(get(call_arguments(node), 1, nothing), :->)
        return all_iterated(call_arguments(node)[2:end]), nested(first(call_arguments(node)))
    end
    if is_broadcast(node) && Meta.isexpr(first(node.args), :->)
        return all_iterated(call_arguments(node)), nested(first(node.args))
    end
    return Union{Symbol, Expr}[], Expr[]
end

"""Whether parsed expression `node` scans all of `collection`: `count(f, xs)`, `findfirst(f, xs)`, `x in xs` and the like."""
scans(collection::Union{Symbol, Expr}, node::Expr)::Bool = callee(node) in SCANS && any(isequal(collection), call_arguments(node))

"""Whether broadcast argument `argument` shields the collection `name` from the broadcast: a one-tuple `(xs,)`, or a call of `Ref` on it."""
shields(name::Any, argument::Any)::Bool = # lint: runtime-dispatch  Expr nodes hold untyped arguments
    (Meta.isexpr(argument, :tuple, 1) || (Meta.isexpr(argument, :call, 2) && callee(argument) === :Ref)) && last(argument.args) == name

"""Whether broadcast argument `name` is a collection that another of the `arguments` shields."""
is_shielded(arguments::AbstractVector, name::Any)::Bool = is_name(name) && any(Base.Fix1(shields, name), arguments) # lint: runtime-dispatch  Expr nodes hold untyped arguments

"""The collections a broadcast scan `node` searches once per element of themselves: `in.(xs, (xs,))`, with the second `xs` shielded."""
function shielded_scans(node::Expr)::Vector{Union{Symbol, Expr}} # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if !is_broadcast(node) || !(callee(node) in SCANS)
        return Union{Symbol, Expr}[]
    end
    return convert(Vector{Union{Symbol, Expr}}, filter(Base.Fix1(is_shielded, call_arguments(node)), call_arguments(node)))
end

"""The named collections that parsed expression `node` scans once per element of themselves."""
function quadratic_collections(node::Expr)::Vector{Union{Symbol, Expr}}
    collections, body = element_loop(node)
    return unique([filter(Base.Fix2(scanned_in, body), collections); shielded_scans(node)])
end

"""Whether one of the expressions `body` scans all of `collection`."""
scanned_in(collection::Union{Symbol, Expr}, body::AbstractVector{Expr})::Bool = any(Base.Fix1(scans, collection), body)

"""The sites of the quadratic scans at `item` of `source`, one per collection scanned."""
function scan_sites(source::Source, item::Located)::Vector{Site}
    key, path, line = "$(source.name) $(item.enclosing)", source.path, item.line
    return [
        Site(key, path, line, "scans `$collection` once per element of `$collection`; group it once (a Dict, or sort and searchsorted)")
            for collection in quadratic_collections(item.node)
    ]
end

"""
Loops, comprehensions, generators, anonymous functions mapped over a collection, and broadcasts that
scan that same collection per element (`count`, `filter`, `findfirst`, `in`, …): quadratic in its
length. Keyed by file and the function they sit in.
"""
quadratic_scans(source::Source)::Vector{Site} = collect(Site, Iterators.flatten(scan_sites.((source,), source.located)))

"""The `open` modes that write to the file."""
const WRITE_MODES = ("w", "a", "w+", "a+", "r+")

"""The `open` keywords that write to the file when `true`."""
const WRITE_KEYWORDS = (:write, :append, :truncate)

"""Every name in parsed expression `node`."""
mentioned(node::Symbol)::Vector{Symbol} = [node]
mentioned(node::Expr)::Vector{Symbol} = collect(Symbol, Iterators.flatten(mentioned.(node.args))) # lint: runtime-dispatch  Expr nodes hold untyped arguments
mentioned(::Any)::Vector{Symbol} = Symbol[]

"""The names the iteration `headers` bind per element: `x` in `x in xs`, `index` and `item` in `(index, item) in enumerate(xs)`."""
header_variables(headers::AbstractVector)::Vector{Symbol} = # lint: runtime-dispatch  Expr nodes hold untyped arguments
    collect(Symbol, Iterators.flatten([mentioned(first(spec.args)) for spec in collect(Expr, Iterators.flatten(iteration_specs.(headers)))]))

"""The names an element loop `node` (as `element_loop` reads it) binds per element: its iteration variables, or its anonymous function's arguments."""
function loop_variables(node::Expr)::Vector{Symbol} # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if node.head === :for
        return header_variables(node.args[1:1])
    end
    if node.head === :generator
        return header_variables(node.args[2:end])
    end
    if node.head === :do
        return mentioned(first(node.args[2].args))
    end
    if is_broadcast(node)
        return mentioned(first(first(node.args).args))
    end
    return mentioned(first(first(call_arguments(node)).args))
end

"""Whether `open` call `node` opens its file to write: a mode `"w"`, `"a"`, `"w+"`, `"a+"` or `"r+"`, or `write`, `append` or `truncate` set to `true`."""
function opens_to_write(node::Expr)::Bool # lint: abstract-local # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    keywords = collect(Any, Iterators.flatten([argument.args for argument in node.args if Meta.isexpr(argument, :parameters)]))
    return any(in(WRITE_MODES), filter(Base.Fix2(isa, String), call_arguments(node))) ||
        any(keyword -> Meta.isexpr(keyword, :kw) && first(keyword.args) in WRITE_KEYWORDS && last(keyword.args) === true, keywords)
end

"""Whether parsed expression `node` writes a file whose path mentions one of `variables`: `write(path, text)`, or `open(path, "w")`."""
function writes_per_element(variables::AbstractVector{Symbol}, node::Expr)::Bool # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if node.head !== :call || isempty(call_arguments(node))
        return false
    end
    if callee(node) === :write
        return !isdisjoint(mentioned(first(call_arguments(node))), variables)
    end
    return callee(node) === :open && opens_to_write(node) &&
        !isdisjoint(collect(Symbol, Iterators.flatten(mentioned.(call_arguments(node)))), variables)
end

"""
Whether parsed expression `node` writes several files one after another: `write.(paths, texts)`,
`foreach(write, paths, texts)`, or a loop whose body writes or opens to write a path built from its
iteration variable.
"""
function writes_in_turn(node::Expr)::Bool # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    if is_broadcast(node) && callee(node) === :write
        return true
    end
    if node.head === :call && callee(node) in (:foreach, :map) && get(call_arguments(node), 1, nothing) === :write
        return true
    end
    body = last(element_loop(node))
    return !isempty(body) && any(Base.Fix1(writes_per_element, loop_variables(node)), body)
end

"""The lines of the functions among `located` that stage their writes: they call `mv` or `rename`, so each write can go to a temporary file first."""
staging_functions(located::AbstractVector{Located})::Vector{Int} =
    unique([item.enclosing_line for item in located if callee(item.node) in (:mv, :rename)])

"""Whether `item` writes several files in turn inside a function whose line is none of `staged` (`staging_functions`)."""
writes_unstaged(staged::AbstractVector{Int}, item::Located)::Bool = writes_in_turn(item.node) && !(item.enclosing_line in staged)

"""
Writes of several files one after another, keyed by file and the function they sit in: a failure
halfway leaves some files rewritten and the rest not. A function that calls `mv` or `rename` stages
its writes and passes: compute every text, write each to a temporary file, then rename them all.
"""
function non_atomic_writes(source::Source)::Vector{Site}
    (; path, name, located) = source
    return [
        Site("$name $(item.enclosing)", path, item.line, "writes several files in turn; write temporary files, then rename them all")
            for item in filter(Base.Fix1(writes_unstaged, staging_functions(located)), located)
    ]
end

# Code rules checked on a loaded module and on its repository's Julia source: lowered code,
# bindings, types and parsed text. Each rule reports its sites through `ratchet!`.

const SYNTAX = Base.JuliaSyntax

"""Definitions, not state: a `DataType` is itself `ismutable`."""
is_definition(value::Any)::Bool = value isa Union{Type, Function, Module}

"""
    is_hidden_input(binding)

Whether reading the global `binding` reads something besides an immutable constant:
a non-constant binding, a mutable value (a `Ref`, `Dict`, cache, `Array`, `Atomic`),
or a `ScopedValue`, whose value depends on the caller's scope rather than the
arguments. Strings, symbols and regexes are immutable in use.
"""
function is_hidden_input(binding::GlobalRef)::Bool # lint: abstract-local  reflects on values of unknown type
    if !isdefined(binding.mod, binding.name)
        return false
    end
    value = getfield(binding.mod, binding.name)
    if is_definition(value) || value isa Union{AbstractString, Symbol, Regex}
        return false
    end
    return !isconst(binding.mod, binding.name) ||
        ismutable(value) ||
        value isa Base.ScopedValues.ScopedValue
end

"""Every global `node`, a lowered statement, reads."""
global_reads(node::GlobalRef)::Vector{GlobalRef} = [node]
global_reads(node::Expr)::Vector{GlobalRef} = GlobalRef[
    read
        for argument in node.args
        for read in global_reads(argument)
]
global_reads(node::Any)::Vector{GlobalRef} = GlobalRef[]

"""
    is_closure_type(value)

Whether binding `value` is a lowered anonymous function, `do` block or inner function
(its type name starts with `#`).
"""
function is_closure_type(value::Any)::Bool # lint: abstract-local  reflects on values of unknown type
    if !(value isa Type)
        return false
    end
    unwrapped = Base.unwrap_unionall(value)
    return unwrapped isa DataType &&
        unwrapped <: Function &&
        startswith(string(unwrapped.name.name), "#")
end

"""
    defined_methods(mod)

The methods `mod` defines on its own functions and types, closures included: each
function's methods, and each type's constructors and call methods. Methods `mod` adds to
a function of a loaded module (`Base.show`, AD rules) count too.
"""
function defined_methods(mod::Module)::Vector{Method} # lint: abstract-local  reflects on values of unknown type
    values = vcat(module_bindings(mod), loaded_functions())
    world = Base.get_world_counter()
    found = reduce(
        vcat,
        vcat(binding_methods.(values, Function), call_methods.(values, world), binding_methods.(values, Type));
        init = Method[],
    )
    return unique(found[[method.module for method in found] .=== (mod,)])
end

"""Every function bound in `Base`, `Core` or a loaded module: where `mod` may add methods."""
loaded_functions()::AbstractVector = reduce(
    vcat,
    filter(Base.Fix2(isa, Function), module_bindings(loaded)) for loaded in unique([Base; Core; collect(values(Base.loaded_modules))]);
    init = [],
)

"""The values bound to the names of `mod`, unexported and compiler-made names included."""
module_bindings(mod::Module)::AbstractVector = getfield.((mod,), filter(Base.Fix1(isdefined, mod), names(mod; all = true)))

# The helpers below take each binding as a call argument: a closure capturing a type or function
# specializes on it, and one compile per binding of the checked package dominated a run.
"""The methods of binding `value` when it is a `kind`: a function's methods, or a type's constructors."""
function binding_methods(@nospecialize(value::Any), kind::Type)::Vector{Method}
    if !(value isa kind)
        return Method[]
    end
    return collect(Method, methods(value))
end

"""The methods that call an instance of binding `value` when it is a struct type; none otherwise."""
function call_methods(@nospecialize(value::Any), world::Integer)::Vector{Method}
    if !(value isa Type && Base.unwrap_unionall(value) isa DataType)
        return Method[]
    end
    return Method[match.method for match in Base._methods_by_ftype(Tuple{Base.unwrap_unionall(value), Vararg}, -1, world)]
end

"""The name of the type whose instances `method` is called on (its function's type), or `nothing`."""
callee_name(method::Method)::Union{Core.TypeName, Nothing} = callee_name(Base.unwrap_unionall(method.sig).parameters[1])
callee_name(callee::TypeVar)::Union{Core.TypeName, Nothing} = callee_name(callee.ub)
callee_name(callee::UnionAll)::Union{Core.TypeName, Nothing} = callee_name(Base.unwrap_unionall(callee))
callee_name(callee::DataType)::Core.TypeName = callee.name
callee_name(::Any)::Nothing = nothing

"""The closure types of `mod` that lowered statements `code` name, by type name."""
function named_closures(code::Core.CodeInfo, mod::Module)::Vector{Core.TypeName}
    reads = filter(Base.Fix2(names_closure, mod), reduce(vcat, global_reads.(code.code); init = GlobalRef[]))
    return Core.TypeName[Base.unwrap_unionall(called_type(value)).name for value in getfield.((mod,), [read.name for read in reads])]
end

"""Whether global `read` names an `is_unnamed_function_type` of `mod`."""
names_closure(read::GlobalRef, mod::Module)::Bool =
    read.mod === mod && isdefined(mod, read.name) && is_unnamed_function_type(called_type(getfield(mod, read.name)))

"""The type a lowered statement names through binding `value`: the type itself, or a function instance's type (a keyword body)."""
called_type(value::Type)::Type = value
called_type(value::Any)::Type = typeof(value)

"""
Whether binding `value` is the type of a closure, `do` block, inner or anonymous function: an
`is_closure_type` that is not the type of a function named in source. Julia 1.12 binds a named
function's type too (`#add_slope!` beside `add_slope!`), and code reaches that function
through its name, not its type.
"""
function is_unnamed_function_type(value::Any)::Bool # lint: abstract-local  reflects on values of unknown type
    if !is_closure_type(value)
        return false
    end
    type = Base.unwrap_unionall(value)
    return !(isdefined(type, :instance) && !startswith(string(nameof(type.instance)), "#"))
end

"""The names of every `is_unnamed_function_type` bound in `mod`, live or left over."""
closure_type_names(mod::Module)::Set{Core.TypeName} = Set{Core.TypeName}(
    Base.unwrap_unionall(value).name for value in module_bindings(mod) if is_unnamed_function_type(value)
)

"""
    live_closures(mod, methods)

The closure types (by name) that the current code of `methods` can create: those the lowered code
of a method that is not itself a closure names, and those a live closure's own code names. A
closure whose defining method was redefined in this process (by Revise, in a worker reused across
trees) is a leftover type that no current code reaches, and is not the source's.
"""
function live_closures(mod::Module, methods::AbstractVector{Method})::Set{Core.TypeName} # lint: abstract-local  lowered IR statements are untyped
    closure_names = closure_type_names(mod)
    created = Dict{Core.TypeName, Set{Core.TypeName}}()
    roots = Set{Core.TypeName}()
    for method in methods
        name = callee_name(method)
        if name in closure_names
            created[name] = union(get(created, name, Set{Core.TypeName}()), created_closures(method, mod))
        else
            roots = union(roots, created_closures(method, mod))
        end
    end
    return fixed_reach(roots, created)
end

"""Closure types (by name) that the lowered code of `method` creates."""
function created_closures(method::Method, mod::Module)::Vector{Core.TypeName}
    code = lowered(method)
    if code isa Core.CodeInfo
        return named_closures(code, mod)
    end
    return Core.TypeName[]
end

"""`live` closed under `created`: every closure a member's own code creates, repeated until none is new."""
function fixed_reach(live::Set{T}, created::AbstractDict{T, Set{T}})::Set{T} where {T}
    grown = union(live, get.((created,), collect(live), (Set{T}(),))...)
    if grown == live
        return live
    end
    return fixed_reach(grown, created)
end

"""
    module_methods(mod)

The `defined_methods` of `mod` that its current code reaches: every method except a closure's that
is not `live_closures`.
"""
function module_methods(mod::Module)::Vector{Method}
    methods = defined_methods(mod)
    live = live_closures(mod, methods)
    return methods[reached.(methods, (closure_type_names(mod),), (live,))]
end

"""Whether current code reaches `method`: it is no closure's (`closure_names`), or its closure is `live`."""
reached(method::Method, closure_names::AbstractSet{Core.TypeName}, live::AbstractSet{Core.TypeName})::Bool =
    !(callee_name(method) in closure_names) || callee_name(method) in live

"""Lowered code of `method`, or `nothing` for a generated or builtin method."""
function lowered(method::Method)::Union{Core.CodeInfo, Nothing}
    if !isdefined(method, :source)
        return nothing
    end
    return Base.uncompressed_ir(method)
end

"""
    statement_line(code, method, index)

The line of `method`'s source that lowered statement `index` of `code` comes from: the line of the
method itself for a statement from another file (a macro's).
"""
function statement_line(code::Core.CodeInfo, method::Method, index::Integer)::Int
    file = method.file
    own_lines = [node.line for node in Base.IRShow.buildLineInfoNode(code.debuginfo, method, index) if node.file === file]
    return get(own_lines, 1, method.line)
end

"""
    hidden_inputs(repository, mod)

Each read of a global that some method of `mod` takes besides its arguments and immutable
constants, keyed by the global and placed at the statement that reads it.
"""
hidden_inputs(repository::Repository, mod::Module)::Vector{Site} =
    reduce(vcat, method_hidden_inputs.(filter(Base.Fix1(in_repository, repository), module_methods(mod))); init = Site[])

"""Whether `method` is defined in a file under the repository's root."""
in_repository(repository::Repository, method::Method)::Bool = startswith(string(method.file), repository.root)

"""The `hidden_inputs` sites of `method`'s lowered code; none for a method without one."""
function method_hidden_inputs(method::Method)::Vector{Site}
    code = lowered(method)
    if isnothing(code)
        return Site[]
    end
    return reduce(vcat, statement_hidden_inputs.((code,), (method,), collect(pairs(code.code))); init = Site[])
end

"""The `hidden_inputs` sites of the lowered statement `entry` (index => statement) of `method`'s `code`."""
function statement_hidden_inputs(code::Core.CodeInfo, method::Method, entry::Pair)::Vector{Site}
    reads = filter(is_hidden_input, global_reads(last(entry)))
    if isempty(reads)
        return Site[]
    end
    return Site.(string.([read.name for read in reads]), string(method.file), statement_line(code, method, first(entry)), "")
end

"""
A method of the package with its unoptimized typed code and whether inference found its return type
to be `Nothing` (after widening, so a constant result `nothing` counts).
"""
struct Inferred
    method::Method
    code::Core.CodeInfo
    returns_nothing::Bool
end

"""
Each method of `mod` (`module_methods`) that inference reaches from `signatures`, typed over each signature
that selects it. The result depends on `signatures` alone. Inference returns a method and its declared type,
with no code, for one it cannot type (a generated method); that has no locals to report and is left out.
"""
function inferred_methods(mod::Module, signatures::AbstractVector{<:Type})::Vector{Inferred}
    methods = Set{Method}(module_methods(mod))
    return reduce(vcat, signature_inferred.(unique(signatures), (methods,)); init = Inferred[])
end

"""The `Inferred` of each method in `methods` that `signature` selects, typed over it."""
function signature_inferred(signature::Type, methods::AbstractSet{Method})::Vector{Inferred}
    typed = filter(Base.Fix2(typed_method_in, methods), Base.code_typed_by_type(signature; optimize = false))
    return Inferred[Inferred(code.parent.def, code, Core.Compiler.widenconst(result) === Nothing) for (code, result) in typed]
end

"""Whether `entry`, a `code_typed_by_type` result, has code for one of `methods`."""
typed_method_in(entry::Pair, methods::AbstractSet{Method})::Bool =
    first(entry) isa Core.CodeInfo && first(entry).parent isa Core.MethodInstance && first(entry).parent.def in methods

"""The slots of `code` that a `catch` binds, which Julia always types `Any`."""
function caught_slots(code::Core.CodeInfo)::Set{Int} # lint: abstract-local  lowered IR statements are untyped
    caught = Set{Int}()
    exceptions = Set{Int}(
        index
            for (index, statement) in enumerate(code.code)
            if statement isa Expr && statement.head === :the_exception
    )
    for statement in code.code
        if statement isa Expr &&
                statement.head === :(=) &&
                statement.args[1] isa Core.SlotNumber &&
                (
                (
                    statement.args[2] isa Core.SSAValue &&
                        statement.args[2].id in exceptions
                ) ||
                    (
                    statement.args[2] isa Expr &&
                        statement.args[2].head === :the_exception
                )
            )
            push!(caught, statement.args[1].id)
        end
    end
    return caught
end

# The logger a `@debug` or `@info` expansion looks up, which is a union of an abstract type by design.
const LOGGER_TYPE = Union{Nothing, Base.CoreLogging.AbstractLogger}

"""
Whether inferred type `inferred` leaves the compiler without a concrete layout: abstract, a `Union`
of more than `UNION_SPLIT_LIMIT` types or of any abstract one, or a collection or tuple that holds such
elements (`Vector{Any}`). `Type{X}` is a value; a local never assigned (`Union{}`) holds nothing.
"""
function abstract_local_type(inferred::Any)::Bool # lint: abstract-local  reflects on values of unknown type
    type = Core.Compiler.widenconst(inferred)
    if type === Union{}
        return false
    elseif type isa Union
        members = Base.uniontypes(type)
        return length(members) > UNION_SPLIT_LIMIT || any(abstract_local_type, members)
    elseif type <: Type
        return false
    elseif type isa DataType && type <: Tuple && length(type.parameters) == 1 && Base.isvarargtype(only(type.parameters))
        return abstract_local_type(only(type.parameters).T)
    elseif !isconcretetype(type)
        return true
    elseif type <: AbstractArray
        return abstract_local_type(eltype(type))
    elseif type <: AbstractDict
        return abstract_local_type(keytype(type)) || abstract_local_type(valtype(type))
    elseif type <: Tuple
        return any(abstract_local_type, fieldtypes(type))
    end
    return false
end

# A `Union` of at most this many concrete types is split at each use, as `Union{Nothing, X}` is.
const UNION_SPLIT_LIMIT = 4

"""
The first lowered statement of `inferred` that assigns slot `index`: where the variable is introduced,
placed on its source line (the method's own line when no statement assigns it).
"""
function slot_line(inferred::Inferred, index::Integer)::Int # lint: abstract-local  lowered IR statements are untyped
    for (position, statement) in pairs(inferred.code.code)
        if statement isa Expr &&
                statement.head === :(=) &&
                statement.args[1] === Core.SlotNumber(index)
            return statement_line(inferred.code, inferred.method, position)
        end
    end
    return inferred.method.line
end

"""The key an offender of a method goes under: its file and name, the file and "anonymous function" for a closure (whose name carries compiler counters)."""
function method_key(method::Method)::String
    name = string(method.name)
    if startswith(name, "#")
        name = "anonymous function"
    end
    return "$(basename(string(method.file))) $name"
end

"""
One site per key, file and lines of `sites`, in first-seen order, its detail the sorted details of all the sites it replaces,
so neither the specialization order nor a second variable on the line changes what the log says.
"""
function one_per_line(sites::AbstractVector{Site})::Vector{Site}
    places = unique([(site.key, site.file, site.line, site.last_line) for site in sites])
    return place_site.((sites,), places)
end

"""The one site of `sites` at `place` (key, file and lines), its detail theirs sorted and joined."""
function place_site(sites::AbstractVector{Site}, place::Tuple{String, String, Int, Int})::Site
    placed = sites[[(site.key, site.file, site.line, site.last_line) for site in sites] .== (place,)]
    return Site(place..., join(sort!(unique([site.detail for site in placed])), "; "))
end

"""
Each named local variable (not an argument) of `repository`'s own methods whose inferred type is
`abstract_local_type`, one site per variable however many specializations ran. A method a macro generated in another package's file
(`@concrete`'s constructors) and a compiler's unnamed slot are not the repository's variables.
"""
function abstract_locals(
        repository::Repository,
        inferred::AbstractVector{Inferred},
    )::Vector{Site}
    own = inferred[startswith.([string(item.method.file) for item in inferred], repository.root)]
    return one_per_line(reduce(vcat, abstract_local_sites.(own); init = Site[]))
end

"""The `abstract_locals` sites of `item`, one per abstract named local."""
function abstract_local_sites(item::Inferred)::Vector{Site}
    slots = collect(eachindex(item.code.slotnames))
    flagged = abstract_slot.((item,), (caught_slots(item.code),), slots, item.code.slotnames, item.code.slottypes)
    details = "local `" .* string.(item.code.slotnames[flagged]) .* "`::" .* string.(item.code.slottypes[flagged])
    return Site.(method_key(item.method), string(item.method.file), slot_line.((item,), slots[flagged]), details)
end

"""Whether slot `index` of `item`, named `name` and inferred `type`, is a named local (not an argument nor `caught`) of `abstract_local_type`."""
abstract_slot(item::Inferred, caught::AbstractSet{Int}, index::Integer, name::Symbol, type::Any)::Bool =
    index > item.method.nargs && !isempty(string(name)) && !startswith(string(name), "#") &&
    type != LOGGER_TYPE && !(index in caught) && abstract_local_type(type)

"""Whether statement `statement` calls one of the arguments `arguments` (slot numbers) of its method."""
calls_argument(statement::Expr, arguments::AbstractUnitRange)::Bool =
    statement.head === :call && first(statement.args) isa Core.SlotNumber && first(statement.args).id in arguments
calls_argument(statement::Any, arguments::AbstractUnitRange)::Bool = false

"""
Whether a `return` in `method`'s lowered code returns a call to one of its arguments (`f()` in
`wrap(f) = f()`): its result is that argument's, so the types its callers passed decide nothing.
"""
function returns_argument_call(method::Method)::Bool
    code = lowered(method)
    if isnothing(code)
        return false
    end
    return any(returns_call.((code,), (2:method.nargs,), code.code))
end

"""Whether lowered `statement` of `code` returns a call to one of the `arguments` (slot numbers)."""
returns_call(code::Core.CodeInfo, arguments::AbstractUnitRange, statement::Any)::Bool =
    statement isa Core.ReturnNode && isdefined(statement, :val) && statement.val isa Core.SSAValue &&
    calls_argument(code.code[statement.val.id], arguments)

"""
Whether `item` is a named function of `repository`, not a closure or another package's function
(`Base.show`, a keyword call), that inference types as always returning `nothing` yet whose name
does not end in `!`: it exists for its effect, so its name says so. `__init__` is exempt, since Julia
fixes its name. A method returning a call to its
argument (`returns_argument_call`) gets no verdict: its callers' arguments decide its result.
"""
function is_unmarked_effect(repository::Repository, item::Inferred)::Bool # lint: abstract-local  lowered IR statements are untyped
    function_type = Base.unwrap_unionall(item.method.sig).parameters[1]
    name = string(item.method.name)
    return item.returns_nothing &&
        !startswith(name, "#") &&
        !endswith(name, "!") &&
        name != "__init__" &&
        function_type isa DataType &&
        function_type <: Function &&
        function_type.name.module === item.method.module &&
        startswith(string(item.method.file), repository.root) &&
        !returns_argument_call(item.method)
end

"""
Each method of `is_unmarked_effect` whose function has no method that returns a value, one site at its
signature however many specializations ran: a function with a `nothing` method beside real ones (a
dispatch on "off") is not a procedure.
"""
function unmarked_effects( # lint: abstract-local  lowered IR statements are untyped
        repository::Repository,
        inferred::AbstractVector{Inferred},
    )::Vector{Site}
    valued = Set(
        (item.method.module, item.method.name)
            for item in inferred
            if !item.returns_nothing
    )
    effects = inferred[is_unmarked_effect.((repository,), inferred) .& .!in.([(item.method.module, item.method.name) for item in inferred], (valued,))]
    return unique([Site(method_key(item.method), string(item.method.file), item.method.line, "") for item in effects])
end

"""Each closure type that the lowered code of `methods` names, with a method that names it."""
closure_namers(mod::Module, methods::AbstractVector{Method})::Dict{Core.TypeName, Method} = Dict{Core.TypeName, Method}(
    reduce(vcat, method_namings.(methods, (mod,)); init = Pair{Core.TypeName, Method}[]),
)

"""Each closure type `method`'s lowered code names (`created_closures`), paired with `method`."""
method_namings(method::Method, mod::Module)::Vector{Pair{Core.TypeName, Method}} = created_closures(method, mod) .=> (method,)

"""
The method that creates closure type `name`: its namer in `namers` (`closure_namers`), followed out of
nested closures to the first namer that is not itself a closure.
"""
function closure_definer(name::Core.TypeName, namers::AbstractDict{Core.TypeName, Method})::Method # lint: abstract-local  lowered IR statements are untyped
    definer = namers[name]
    outer = callee_name(definer)
    if haskey(namers, outer)
        return closure_definer(outer, namers)
    end
    return definer
end

"""
    closure_site(type, definer, world, detail)

The site of closure type `type`, created by method `definer` (`closure_definer`), keyed by `definer`'s file
and name (`method_key`) because closure type names carry compiler counters. It sits at the closure's call
method, or at `definer` when that method has no source file (code built without line numbers).
"""
function closure_site(type::DataType, definer::Method, world::Integer, detail::AbstractString)::Site # lint: abstract-local  lowered IR statements are untyped
    matches = Base._methods_by_ftype(Tuple{type, Vararg}, -1, world)
    placed = definer
    if !isempty(matches) && first(matches).method.file !== :none
        placed = first(matches).method
    end
    return Site(method_key(definer), string(placed.file), placed.line, String(detail))
end

# These helpers pass each type as an argument: a closure capturing a type specializes on it.
"""The declared field types of `type`, type variables included."""
field_types(type::DataType)::Vector{Union{Type, TypeVar}} = fieldtype.((type,), 1:fieldcount(type))

"""
Whether a capture of type `type` is plain immutable data: a non-function `isbits` value, a `String`
or `Symbol`, or an immutable struct, tuple or small `Union` of such. Arrays, `Ref`s, mutable structs,
types, functions, modules and `Core.Box` are not.
"""
plain_capture(@nospecialize(type::Any))::Bool = false
plain_capture(type::Union)::Bool = all(plain_capture, Base.uniontypes(type))
function plain_capture(type::DataType)::Bool
    if type <: Union{Function, Type, Module, Core.Box} || !isconcretetype(type)
        return false
    end
    if type === String || type === Symbol || isbitstype(type)
        return true
    end
    return !ismutabletype(type) && all(plain_capture, field_types(type))
end

"""The closure types `Base.specializations` records for the call methods of closure `type`: one per instance the package compiled."""
closure_instances(type::DataType, world::Integer)::Vector{Type} = unique(
    reduce(vcat, instance_callees.(Base._methods_by_ftype(Tuple{type, Vararg}, -1, world)); init = Type[]),
)

"""The function type each specialization of `match`'s method was compiled for."""
instance_callees(match::Core.MethodMatch)::Vector{Type} =
    Type[first(Base.unwrap_unionall(instance.specTypes).parameters) for instance in Base.specializations(match.method)]

"""
The kind of fault a capture of type `capture` is, in a compiled closure instance: `:plain` for
`plain_capture` data, `:overspecialized` for a type or function (one compile per value), `:impure` for
other concrete data (mutable state or a module), `:unstable` for a type inference left abstract.
"""
function capture_kind(@nospecialize(capture::Any))::Symbol
    if plain_capture(capture)
        return :plain
    end
    # A type capture is `Type{Int}`, or `Core.TypeEgal{Int}` (not a DataType) from Julia 1.14; neither is concrete.
    if capture isa Type && capture <: Union{Type, Function}
        return :overspecialized
    end
    if (capture isa DataType && isconcretetype(capture)) || (capture isa Union && all(isconcretetype, Base.uniontypes(capture)))
        return :impure
    end
    return :unstable
end

"""What a capture of type `capture` with fault `kind` (`capture_kind`) costs, for the site's detail."""
function capture_detail(kind::Symbol, @nospecialize(capture::Any))::String
    if kind === :overspecialized
        return "captures $capture, so it compiles once per value; pass it as an argument"
    end
    if kind === :unstable
        return "captures $capture, a type inference left abstract"
    end
    return "captures $capture, not plain immutable data"
end

"""The faults of closure instance `instance`, as `kind => detail` pairs (`capture_kind`, `capture_detail`)."""
function instance_faults(@nospecialize(instance::Any))::Vector{Pair{Symbol, String}}
    if !(instance isa DataType && isconcretetype(instance))
        return [:unstable => "built where the types of its captures are unknown"]
    end
    captures = field_types(instance)
    kinds = capture_kind.(captures)
    return [kind => capture_detail(kind, capture) for (kind, capture) in zip(kinds, captures) if kind !== :plain]
end

"""
The faults of closure `type`, as `kind => detail` pairs: a `Core.Box` or no compiled instance (its captures
unverified) is `:impure`; otherwise the `instance_faults` of every instance. None for a closure that
captures nothing, or only `plain_capture` data in every instance.
"""
function closure_faults(type::DataType, world::Integer)::Vector{Pair{Symbol, String}}
    declared = field_types(type)
    if isempty(declared)
        return Pair{Symbol, String}[]
    end
    if Core.Box in declared
        return [:impure => "holds a Core.Box: a captured variable is rebound"]
    end
    instances = closure_instances(type, world)
    if isempty(instances)
        return [:impure => "no compiled instance, so its captures are unverified; cover it in the precompile workload"]
    end
    return unique(reduce(vcat, instance_faults.(instances); init = Pair{Symbol, String}[]))
end

"""The details of the `faults` (`closure_faults`) of kind `kind`, joined; empty when there are none."""
kind_detail(faults::AbstractVector{Pair{Symbol, String}}, kind::Symbol)::String = join(last.(faults[first.(faults) .=== kind]), "; ")

"""The closure types the current code of `mod` can create (`live_closures`), unwrapped."""
function live_closure_types(mod::Module)::Vector{DataType}
    live = live_closures(mod, defined_methods(mod))
    closures = DataType[Base.unwrap_unionall(value) for value in module_bindings(mod) if is_closure_type(value)]
    return closures[in.([type.name for type in closures], (live,))]
end

"""
Each `live_closure_types` closure of `mod` with a fault of kind `kind` (`closure_faults`), as a
`closure_site` whose detail is the fault. A closure that captures nothing, like `x -> x.field`, passes.
"""
function anonymous_function_sites(mod::Module, kind::Symbol)::Vector{Site}
    world = Base.get_world_counter()
    namers = closure_namers(mod, defined_methods(mod))
    types = live_closure_types(mod)
    details = kind_detail.(closure_faults.(types, world), kind)
    faulty = .!isempty.(details)
    definers = closure_definer.([type.name for type in types[faulty]], (namers,))
    return closure_site.(types[faulty], definers, world, details[faulty])
end

"""Anonymous functions of `mod` that capture mutable state, hold a `Core.Box`, or were never compiled."""
impure_anonymous_functions(mod::Module)::Vector{Site} = anonymous_function_sites(mod, :impure)

"""Anonymous functions of `mod` built where inference could not pin down the types of their captures."""
unstable_anonymous_functions(mod::Module)::Vector{Site} = anonymous_function_sites(mod, :unstable)

"""Anonymous functions of `mod` that capture a type or function, so each value compiles a new instance."""
overspecialized_anonymous_functions(mod::Module)::Vector{Site} = anonymous_function_sites(mod, :overspecialized)

"""Struct types `mod` defines, closures excluded; a type bound to two names counts once."""
function module_structs(mod::Module)::Vector{DataType}
    structs = DataType[Base.unwrap_unionall(value) for value in module_bindings(mod) if is_struct_binding(value)]
    return unique(structs[parentmodule.(structs) .=== (mod,)])
end

"""Whether binding `value` is a struct type, closures excluded."""
is_struct_binding(@nospecialize(value::Any))::Bool = value isa Type && !is_closure_type(value) &&
    Base.unwrap_unionall(value) isa DataType && isstructtype(Base.unwrap_unionall(value))

"""The `module_structs` of `mod` declared mutable."""
mutable_structs(mod::Module)::Vector{DataType} = filter(ismutabletype, module_structs(mod))

"""
Fields of `type` declared with an abstract type (not a type parameter, not a `Union`), or
with a concrete container of one: `Vector{Any}`, `Base.RefValue{Any}` and
`Dict{Tuple, Any}` are concrete, but every read from them is dynamically dispatched.
"""
function abstract_fields(type::DataType)::Vector{Symbol}
    field_names = collect(Symbol, fieldnames(type))
    return field_names[abstract_declaration.(fieldtype.((type,), field_names))]
end

"""Whether field type `declared` is abstract: not a type parameter, not a `Union`, and `holds_abstract`."""
abstract_declaration(@nospecialize(declared::Any))::Bool = !(declared isa TypeVar) && !(declared isa Union) && holds_abstract(declared)

"""
Whether `declared` is abstract or has an abstract type among its parameters, at any depth.
Allowed: `Union`s (small, split by the compiler), `Type{T}`, a struct's own type parameters
(`Vector{E}` with `E` free), and value parameters (`SVector{16, E}`'s `Tuple{16}`).
"""
function holds_abstract(declared::Type)::Bool # lint: abstract-local  reflects on values of unknown type
    plain = Base.unwrap_unionall(declared)
    abstract_itself = if Base.has_free_typevars(declared) || plain <: Tuple
        plain isa DataType && isabstracttype(plain)
    else
        !isconcretetype(declared)
    end
    return abstract_itself || any(abstract_parameter, plain.parameters)
end

abstract_parameter(parameter::Any)::Bool = parameter isa UnionAll ||
    (parameter isa DataType && !(parameter <: Type) && holds_abstract(parameter))

"""First word of a name in snake case: `SolverControls` and `solver_tolerance` both give `"solver"`."""
first_word(name::Symbol)::String = lowercase(
    first(
        split(
            replace(string(name), r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])" => "_"),
            '_',
        )
    )
)

"""
    repeated_prefix(type)

The word that the field names of `type` repeat instead of saying it once in the type:
the type's own first word starting any field (`SolverControls.solver_tolerance`), or one
first word shared by more than half of at least three fields (`continuation_step`,
`continuation_theta`, ...: those fields belong in a `ContinuationControls`). `nothing`
when no word repeats.
"""
function repeated_prefix(type::DataType)::Union{String, Nothing} # lint: abstract-local  reflects on values of unknown type
    words = String[first_word(name) for name in collect(Symbol, fieldnames(type)) if occursin('_', string(name))]
    own = first_word(nameof(type))
    if own in words
        return own
    end
    fields = fieldcount(type)
    candidates = unique(words)
    shared = candidates[count.(isequal.(candidates), (words,)) .* 2 .> fields]
    if fields >= 3 && !isempty(shared)
        return only(shared)
    end
    return nothing
end

"""The name a parsed function definition `node` defines, or `nothing` when `node` defines none."""
function defined_name(node::Expr)::Union{Symbol, Nothing} # lint: abstract-local  Expr nodes hold untyped arguments
    call = signature_call(node)
    return isnothing(call) ? nothing : Symbol(string(call.args[1]))
end

"""The declared return type of parsed function definition `node`, or `nothing` when it declares none."""
function return_annotation(node::Expr)::Any # lint: abstract-local  Expr nodes hold untyped arguments
    signature = node.args[1]
    while signature isa Expr && signature.head === :where
        signature = signature.args[1]
    end
    if signature isa Expr && signature.head === :(::) && length(signature.args) == 2
        return signature.args[2]
    end
    return nothing
end

"""Whether parsed type expression `annotation` is a `Union` with `Nothing` among its members."""
mentions_nothing(annotation::Expr)::Bool = annotation.head === :curly &&
    first(annotation.args) === :Union &&
    :Nothing in annotation.args[2:end]
mentions_nothing(::Any)::Bool = false

# The edge of `exp`'s Float32 and Float64 ranges, written as a literal guard.
const EXP_RANGE_LITERALS = (88, 709)

"""
Whether parsed source `node` itself is an overflow or underflow guard: a call to `floatmin` or
`floatmax`, a literal at the edge of `exp`'s range, or `isfinite` of an expression calling `exp`.
"""
is_range_guard(node::Real)::Bool = node in EXP_RANGE_LITERALS
is_range_guard(node::Expr)::Bool = node.head === :call &&
    (
    first(node.args) in (:floatmin, :floatmax) ||
        (first(node.args) === :isfinite && any(calls_exp, node.args[2:end]))
)
is_range_guard(::Any)::Bool = false

calls_exp(node::Expr)::Bool = (node.head === :call && first(node.args) === :exp) ||
    any(calls_exp, node.args)
calls_exp(::Any)::Bool = false

"""Parsed source `node` with its line numbers dropped, so two copies of one statement compare equal."""
without_lines(node::Expr)::Expr = Expr(
    node.head,
    (without_lines(argument) for argument in node.args if !(argument isa LineNumberNode))...
)
without_lines(node::Any)::Any = node

"""
One expression of parsed source: `line` is the nearest line marker before it, `enclosing` the
function definition it sits in (`<top level>` outside any) and `enclosing_line` that definition's line.
"""
struct Located
    node::Expr
    line::Int
    enclosing::Symbol
    enclosing_line::Int
end

"""The line a function definition `node` starts on: its body's first line marker, which `Meta.parseall` sets to the `function` line even after a docstring."""
function definition_line(node::Expr, line::Int)::Int
    if length(node.args) >= 2 &&
            node.args[2] isa Expr &&
            node.args[2].head === :block &&
            !isempty(node.args[2].args) &&
            first(node.args[2].args) isa LineNumberNode
        return first(node.args[2].args).line
    end
    return line
end

"""The lines of function definition `node`'s signature: from `definition_line` to the line before its body's first statement (one line for `f(x) = …`)."""
function definition_lines(node::Expr, line::Int)::UnitRange{Int} # lint: abstract-local  Expr nodes hold untyped arguments
    first_line = definition_line(node, line)
    body = length(node.args) >= 2 ? node.args[2] : nothing
    if body isa Expr &&
            body.head === :block &&
            length(body.args) >= 2 &&
            body.args[2] isa LineNumberNode
        return first_line:max(first_line, body.args[2].line - 1)
    end
    return first_line:first_line
end

"""The name of the `@testset` that parsed expression `node` opens, or `nothing` when `node` opens none or the name is interpolated."""
function testset_name(node::Expr)::Union{Symbol, Nothing} # lint: abstract-local  Expr nodes hold untyped arguments
    if node.head === :macrocall && first(node.args) === Symbol("@testset")
        for argument in node.args
            if argument isa String
                return Symbol(argument)
            end
        end
    end
    return nothing
end

"""Every expression below parsed source `node`, each as a `Located`; returns the line the walk ended on."""
function locate!( # lint: abstract-local  Expr nodes hold untyped arguments
        found::Vector{Located},
        node::Expr,
        line::Int,
        enclosing::Symbol,
        enclosing_line::Int,
    )::Int
    name = defined_name(node)
    inside = something(name, testset_name(node), enclosing)
    inside_line = if !isnothing(name)
        definition_line(node, line)
    elseif !isnothing(testset_name(node))
        line
    else
        enclosing_line
    end
    push!(found, Located(node, line, inside, inside_line))
    for argument in node.args
        if argument isa LineNumberNode
            line = argument.line
        elseif argument isa Expr
            line = locate!(found, argument, line, inside, inside_line)
        end
    end
    return line
end

"""Every expression of the parsed file `path`, as `Located`s."""
function located_source(path::AbstractString)::Vector{Located}
    found = Located[]
    locate!(found, Meta.parseall(read(path, String)), 0, Symbol("<top level>"), 0)
    return found
end

"""Functions declaring a `Union{Nothing, …}` return: a "can't compute here" answer, one site per definition."""
function nothing_returns(path::AbstractString, located::AbstractVector{Located})::Vector{
        Site,
    }
    return [
        Site(
            string(defined_name(item.node)),
            path,
            first(definition_lines(item.node, item.line)),
            last(definition_lines(item.node, item.line)),
            "",
        )
            for item in located
            if !isnothing(defined_name(item.node)) &&
            mentions_nothing(return_annotation(item.node))
    ]
end

"""Overflow and underflow guards, keyed by the function they sit in."""
function range_guards(path::AbstractString, located::AbstractVector{Located})::Vector{Site} # lint: abstract-local  Expr nodes hold untyped arguments
    sites = Site[]
    for item in located
        if is_range_guard(item.node)
            push!(sites, Site(string(item.enclosing), path, item.line, ""))
        end
        for argument in item.node.args
            if argument isa Real && is_range_guard(argument)
                push!(sites, Site(string(item.enclosing), path, item.line, ""))
            end
        end
    end
    return sites
end

"""Statements that repeat an earlier statement of the same block, keyed `definition: statement`. A statement pasted twice runs twice; the same line in two branches is in two blocks and passes."""
function repeated_statements( # lint: abstract-local  Expr nodes hold untyped arguments
        path::AbstractString,
        located::AbstractVector{Located},
    )::Vector{Site}
    sites = Site[]
    for item in located
        if item.node.head !== :block
            continue
        end
        seen = Expr[]
        line = item.line
        for argument in item.node.args
            if argument isa LineNumberNode
                line = argument.line
            elseif argument isa Expr
                statement = without_lines(argument)
                if statement in seen
                    push!(sites, Site("$(item.enclosing): $statement", path, line, ""))
                end
                push!(seen, statement)
            end
        end
    end
    return sites
end

"""Calls of `Core.Compiler.return_type`, a guess at a result type, keyed by file."""
function return_type_calls(path::AbstractString, located::AbstractVector{Located})::Vector{
        Site,
    }
    return [
        Site(basename(path), path, item.line, "")
            for item in located
            if item.node.head === :. &&
            length(item.node.args) == 2 &&
            item.node.args[2] == QuoteNode(:return_type)
    ]
end

const STRUCT_KIND = SYNTAX.@K_str "struct"
const CURLY_KIND = SYNTAX.@K_str "curly"
const SUBTYPE_KIND = SYNTAX.@K_str "<:"

"""The name a `struct` syntax node declares, whatever its parameters and supertype, as Julia names the type (`var"Odd Name"` gives `Symbol("Odd Name")`)."""
function struct_name(node::SYNTAX.SyntaxNode)::Symbol
    header = first(SYNTAX.children(node))
    while SYNTAX.kind(header) in (CURLY_KIND, SUBTYPE_KIND)
        header = first(SYNTAX.children(header))
    end
    return Symbol(Expr(header))
end

"""The `struct` syntax nodes at or below `node`, as name => line of the `struct` keyword (never the docstring's line above it)."""
function struct_lines(node::SYNTAX.SyntaxNode)::Vector{Pair{Symbol, Int}}
    if SYNTAX.is_leaf(node)
        return Pair{Symbol, Int}[]
    end
    nested = vcat(Pair{Symbol, Int}[], (struct_lines(child) for child in SYNTAX.children(node))...)
    if SYNTAX.kind(node) === STRUCT_KIND
        return vcat(struct_name(node) => first(SYNTAX.source_location(node)), nested)
    end
    return nested
end

"""Where each struct of the parsed source `files` is declared: its name with the file and line of its `struct` keyword, so a `# lint:` comment on that line opts the struct out even when a docstring sits above it."""
function struct_locations(files::AbstractVector{<:AbstractString})::Dict{Symbol, Tuple{String, Int}}
    return Dict{Symbol, Tuple{String, Int}}(
        name => (file, line) for file in files
            for (name, line) in struct_lines(SYNTAX.parseall(SYNTAX.SyntaxNode, read(file, String); filename = file))
    )
end

const CONCRETE_CONTAINERS = (:Vector, :Matrix, :Array, :Dict)
const RESIZERS = (
    :push!,
    :pushfirst!,
    :append!,
    :prepend!,
    :resize!,
    :empty!,
    :pop!,
    :popfirst!,
    :deleteat!,
    :insert!,
    :splice!,
    :sizehint!,
    :union!,
    :setdiff!,
)

"""Whether parsed type expression `annotation` is a concrete container (`Vector`, `Matrix`, `Array`, `Dict`, bare or with parameters), alone or as a direct member of a `Union`."""
is_concrete_container(annotation::Symbol)::Bool = annotation in CONCRETE_CONTAINERS
function is_concrete_container(annotation::Expr)::Bool
    if annotation.head !== :curly
        return false
    end
    if first(annotation.args) === :Union
        return any(is_concrete_container, annotation.args[2:end])
    end
    return first(annotation.args) in CONCRETE_CONTAINERS
end
is_concrete_container(::Any)::Bool = false

"""Whether parsed `node` resizes the variable `name`: a call of `push!`, `empty!` or another size-changing function on it."""
function resizes(node::Expr, name::Symbol)::Bool # lint: abstract-local  Expr nodes hold untyped arguments
    if node.head === :call &&
            length(node.args) >= 2 &&
            first(node.args) in RESIZERS &&
            node.args[2] === name
        return true
    end
    for argument in node.args
        if argument isa Expr && resizes(argument, name)
            return true
        end
    end
    return false
end

"""The call a parsed function definition `node` declares, whatever return annotation or `where` clause wraps it, or `nothing`."""
function signature_call(node::Expr)::Union{Expr, Nothing} # lint: abstract-local  Expr nodes hold untyped arguments
    if !(node.head in (:function, :(=))) || isempty(node.args)
        return nothing
    end
    signature = node.args[1]
    while signature isa Expr && signature.head in (:where, :(::))
        signature = signature.args[1]
    end
    if signature isa Expr && signature.head === :call
        return signature
    end
    return nothing
end

"""Each annotated argument below parsed `argument`, as its name (`:_` when unnamed) and annotation, positional or keyword."""
function annotated_arguments(argument::Expr)::Vector{Tuple{Symbol, Any}} # lint: abstract-local  Expr nodes hold untyped arguments
    found = Tuple{Symbol, Any}[]
    if argument.head === :(::)
        name = length(argument.args) == 2 ? argument.args[1] : :_
        push!(found, (name isa Symbol ? name : :_, last(argument.args)))
    elseif argument.head in (:kw, :parameters, :...)
        for inner in (argument.head === :kw ? argument.args[1:1] : argument.args)
            if inner isa Expr
                append!(found, annotated_arguments(inner))
            end
        end
    end
    return found
end
annotated_arguments(::Any)::Vector{Tuple{Symbol, Any}} = Tuple{Symbol, Any}[]

"""
Arguments annotated with a concrete container (`is_concrete_container`) that the method does not
resize, one site per argument at the method's signature, keyed by file: `AbstractVector{T}` takes a
view, an `OffsetArray` or a GPU array, a `Vector{T}` takes none of them.
"""
function concrete_arguments(path::AbstractString, located::AbstractVector{Located})::Vector{ # lint: abstract-local  Expr nodes hold untyped arguments
        Site,
    }
    sites = Site[]
    for item in located
        call = signature_call(item.node)
        if isnothing(call) || length(item.node.args) < 2
            continue
        end
        span = definition_lines(item.node, item.line)
        body = item.node.args[2]
        for argument in call.args[2:end]
            for (name, annotation) in annotated_arguments(argument)
                if is_concrete_container(annotation) &&
                        !(body isa Expr && resizes(body, name))
                    push!(sites, Site(basename(path), path, first(span), last(span), ""))
                end
            end
        end
    end
    return sites
end

# Result types that need no generic form: nothing, booleans, tuples and named tuples.
const EXEMPT_RESULT_TYPES = (:Nothing, :Bool, :NamedTuple, :Tuple, :NTuple)

"""
    names_concrete_type(annotation, scope, variables = ())

Whether parsed type expression `annotation` names a concrete type of `scope` or of Base (`Float32`,
`Vector{E}`, a package struct), alone or as a member of a `Union`. A result type must be
generic (`typeof(x)`, a type variable, `AbstractVector{E}`), so a fixed concrete type is named here,
except `Nothing`, `Bool`, tuples and `NamedTuple`s (`EXEMPT_RESULT_TYPES`) and enum types. A type variable,
`typeof(x)` and an abstract type name none. A package struct with a parameter that mentions one of the method's
`where` `variables` (`Result{E}`, `Result{Vector{E}}`) is generic too: it has no abstract form to name instead.
Base's own concrete types stay concrete with such a parameter, since `AbstractVector{E}` names `Vector{E}`'s.
"""
function names_concrete_type(annotation::Symbol, scope::Module, ::Any = ())::Bool # lint: abstract-local  Expr nodes hold untyped arguments
    if annotation in EXEMPT_RESULT_TYPES
        return false
    end
    for source in (scope, Base)
        if isdefined(source, annotation)
            named = getglobal(source, annotation)
            return named isa Type &&
                !(named <: Enum) &&
                Base.unwrap_unionall(named) isa DataType &&
                !isabstracttype(named)
        end
    end
    return false
end
function names_concrete_type(annotation::Expr, scope::Module, variables::Any = ())::Bool # lint: abstract-local  Expr nodes hold untyped arguments
    if annotation.head !== :curly
        return false
    end
    if first(annotation.args) === :Union
        for member in annotation.args[2:end]
            if names_concrete_type(member, scope, variables)
                return true
            end
        end
        return false
    end
    head = first(annotation.args)
    if package_type(head, scope) &&mentions_variable(Expr(:tuple, annotation.args[2:end]...), variables)
        return false
    end
    return names_concrete_type(head, scope, variables)
end
names_concrete_type(::Any, ::Module, ::Any = ())::Bool = false

"""Whether type name `head` resolves in `scope` to a type that neither Base nor Core defines."""
function package_type(head::Symbol, scope::Module)::Bool # lint: abstract-local  Expr nodes hold untyped arguments
    if !isdefined(scope, head)
        return false
    end
    named = getglobal(scope, head)
    return named isa Type && !(parentmodule(named) in (Base, Core))
end
package_type(::Any, ::Module)::Bool = false

"""Whether parsed type expression `parameter` mentions one of the type variables `variables`, at any depth."""
mentions_variable(parameter::Symbol, variables::Any)::Bool = parameter in variables
function mentions_variable(parameter::Expr, variables::Any)::Bool # lint: abstract-local  Expr nodes hold untyped arguments
    for argument in parameter.args
        if mentions_variable(argument, variables)
            return true
        end
    end
    return false
end
mentions_variable(::Any, ::Any)::Bool = false

"""The type variables parsed function definition `node` binds in its `where` clauses (`T` of `T <: Real` included)."""
function where_variables(node::Expr)::Vector{Symbol} # lint: abstract-local  Expr nodes hold untyped arguments
    variables = Symbol[]
    signature = node.args[1]
    while signature isa Expr && signature.head in (:where, :(::))
        if signature.head === :where
            append!(variables, bound_name.(signature.args[2:end]))
        end
        signature = signature.args[1]
    end
    return variables
end

"""The variable a `where` clause entry binds: `T`, `T <: Real` or `T >: Int`."""
bound_name(entry::Symbol)::Symbol = entry
bound_name(entry::Expr)::Symbol = bound_name(first(entry.args))

"""The type name at the head of parsed type expression `annotation` (`Foo` of `Foo{T}`), or `nothing`."""
type_head(annotation::Symbol)::Symbol = annotation
function type_head(annotation::Expr)::Union{Symbol, Nothing}
    if annotation.head === :curly
        return type_head(first(annotation.args))
    end
    return nothing
end
type_head(::Any)::Nothing = nothing

"""Whether method definition `node` is a constructor: it is named for the type its return annotation names, `Foo(…)::Foo` or `Foo{T}(…)::Foo{T}`."""
function constructs_own_type(node::Expr)::Bool
    call = signature_call(node)
    if isnothing(call)
        return false
    end
    returned = type_head(return_annotation(node))
    return !isnothing(returned) && type_head(first(call.args)) === returned
end

"""The repair `ratchet!`'s `fix` names for a `concrete_returns` offender: the result annotations the rule accepts."""
const CONCRETE_RETURN_FIX =
    "annotate the result generically: a type variable the arguments bind (`function f(x::T)::T where {T}`, " *
    "or `(f(x::T)::T) where {T} = …` on one line), `typeof(x)`, or an abstract type " *
    "(`AbstractVector{E}`, `AbstractMatrix{E}`, never `Vector{E}` or `Matrix{E}`)"

"""A `Site` at the definition lines of `item.node` in `path`, keyed by file basename and defined name."""
function definition_site(path::AbstractString, item::Located)::Site
    return Site(
        "$(basename(path)) $(defined_name(item.node))",
        path,
        first(definition_lines(item.node, item.line)),
        last(definition_lines(item.node, item.line)),
        "",
    )
end

"""
Methods whose declared return type names a concrete type (`names_concrete_type`), one site per
method at its signature, keyed by file and function name: a result type must be generic, annotated by
what the arguments bind, not by a fixed type. A package struct parameterized by the method's `where` variables is
generic. A constructor returning its own struct (`constructs_own_type`) is exempt.
"""
function concrete_returns(
        path::AbstractString,
        located::AbstractVector{Located},
        scope::Module,
    )::Vector{Site}
    return definition_site.(path, filter(Base.Fix2(returns_concrete, scope), located))
end

"""Whether the definition `item` declares a return type naming a concrete type of `scope`, and is no constructor of its own type."""
returns_concrete(item::Located, scope::Module)::Bool =
    !isnothing(signature_call(item.node)) && length(item.node.args) >= 2 &&
    names_concrete_type(return_annotation(item.node), scope, where_variables(item.node)) && !constructs_own_type(item.node)

const FLOAT_KIND = SYNTAX.@K_str "Float"
const IDENTIFIER_KIND = SYNTAX.@K_str "Identifier"
const MACROCALL_KIND = SYNTAX.@K_str "macrocall"
const FIELD_KIND = SYNTAX.@K_str "."
const QUOTE_KIND = SYNTAX.@K_str "quote"
# Names that mean Float64: the type, its complex partner, and the Float64 constants.
const FLOAT64_NAMES = (:Float64, :ComplexF64, :Inf, :NaN, :Inf64, :NaN64)

"""
Float64 tokens below syntax `node`, one site each at the token's own line, keyed by file: an untyped
float literal, `Float64`, `ComplexF64`, or the constants `Inf` and `NaN` (also `Inf64`, `NaN64`).
A field name (`Base.Inf`), a quoted symbol and an `@changeprecision` body, which parses at its own
precision, are skipped.
"""
function float64_sites!(
        sites::AbstractVector{Site},
        path::AbstractString,
        node::SYNTAX.SyntaxNode,
    )::Nothing
    kind = SYNTAX.kind(node)
    if SYNTAX.is_leaf(node)
        if kind === FLOAT_KIND ||
                (
                kind === IDENTIFIER_KIND &&
                    Symbol(SYNTAX.sourcetext(node)) in FLOAT64_NAMES
            )
            push!(sites, Site(basename(path), path, first(SYNTAX.source_location(node)), ""))
        end
        return nothing
    end
    children = SYNTAX.children(node)
    if kind === QUOTE_KIND ||
            (
            kind === MACROCALL_KIND &&
                SYNTAX.sourcetext(first(children)) == "@changeprecision"
        )
        return nothing
    end
    for child in (kind === FIELD_KIND ? children[1:1] : children)
        float64_sites!(sites, path, child)
    end
    return nothing
end

"""The Float64 sites of the Julia file `path`, by `float64_sites!`."""
function float64_sites(path::AbstractString)::Vector{Site}
    sites = Site[]
    float64_sites!(
        sites,
        path,
        SYNTAX.parseall(SYNTAX.SyntaxNode, read(path, String); filename = path),
    )
    return sites
end

const CALL_KIND = SYNTAX.@K_str "call"
# C-interop types: they mean something only at a C call, a `Ptr` boundary or a C-layout struct.
const C_TYPE_NAMES = (
    :Cchar, :Cuchar, :Cshort, :Cushort, :Cint, :Cuint, :Clong, :Culong, :Clonglong, :Culonglong,
    :Cfloat, :Cdouble, :Csize_t, :Cssize_t, :Cptrdiff_t, :Cwchar_t, :Cstring, :Cwstring,
)
# Calls and macros whose body is C-facing, where C types belong.
const C_BOUNDARY_NAMES = ("ccall", "cfunction", "@ccall", "@cfunction", "@ccallable")

const REF_NAMES = (:Ref, :RefValue)

"""
Identifiers in syntax `node` named in `names`, one site each at the name's own line, keyed by file,
outside the body of `ccall`, `@ccall`, `cfunction`, `@cfunction` and `@ccallable` (also written
`Base.ccall`). A quoted symbol is skipped; so is a field name (`Base.Cint`) unless `fields` is set.
"""
function name_sites(
        path::AbstractString,
        node::SYNTAX.SyntaxNode,
        names::Tuple{Vararg{Symbol}},
        fields::Bool,
    )::Vector{Site}
    kind = SYNTAX.kind(node)
    if SYNTAX.is_leaf(node)
        if kind === IDENTIFIER_KIND && Symbol(SYNTAX.sourcetext(node)) in names
            return [Site(basename(path), path, first(SYNTAX.source_location(node)), "")]
        end
        return Site[]
    end
    children = SYNTAX.children(node)
    if kind === QUOTE_KIND
        return Site[]
    end
    if kind in (CALL_KIND, MACROCALL_KIND) && last(split(SYNTAX.sourcetext(first(children)), '.')) in C_BOUNDARY_NAMES
        return Site[]
    end
    if kind === FIELD_KIND && !fields
        children = children[1:1]
    end
    return reduce(vcat, (name_sites(path, child, names, fields) for child in children); init = Site[])
end

"""The syntax tree of the Julia file `path`."""
source_tree(path::AbstractString)::SYNTAX.SyntaxNode = SYNTAX.parseall(SYNTAX.SyntaxNode, read(path, String); filename = path)

"""The C-interop type names (`C_TYPE_NAMES`) of the Julia file `path` outside a C call, by `name_sites`."""
c_type_sites(path::AbstractString)::Vector{Site} = name_sites(path, source_tree(path), C_TYPE_NAMES, false)

"""The `Ref` and `RefValue` names (`REF_NAMES`) of the Julia file `path` outside a C call, by `name_sites`."""
ref_sites(path::AbstractString)::Vector{Site} = name_sites(path, source_tree(path), REF_NAMES, true)

"""Whether a parsed argument of a method signature has no `::` annotation (a bare name, alone or with a default or `...`)."""
untyped_argument(argument::Symbol)::Bool = true
function untyped_argument(argument::Expr)::Bool
    if argument.head === :parameters
        # A keyword splat (`; options...`) has no syntax for an annotation.
        return any(
            untyped_argument,
            [
                item
                    for item in argument.args
                    if !(item isa Expr && item.head === :... && first(item.args) isa Symbol)
            ],
        )
    elseif argument.head in (:kw, :...)
        return untyped_argument(first(argument.args))
    end
    return false
end
untyped_argument(::Any)::Bool = false

"""
Whether method definition `node` has an argument with no annotation or declares no return type;
`false` for anything that is not a method definition.
"""
function lacks_annotation(node::Expr)::Bool
    call = signature_call(node)
    if isnothing(call) || length(node.args) < 2
        return false
    end
    return any(untyped_argument, call.args[2:end]) || isnothing(return_annotation(node))
end

"""
Methods that lack an argument annotation or a return type, one site per method at its
signature, keyed by file and function name.
"""
function missing_annotations(
        path::AbstractString,
        located::AbstractVector{Located},
    )::Vector{Site}
    return [
        definition_site(path, item)
            for item in located
            if lacks_annotation(item.node)
    ]
end

"""Whether `name` is one letter long and not among the names `exempt` allows or `_`, which binds nothing."""
is_one_letter(name::Symbol, exempt::Tuple{Vararg{Symbol}})::Bool = length(string(name)) ==
    1 &&
    name !== :_ &&
    !(name in exempt)

"""Each variable name a parsed target binds: an assignment target, a lambda or method parameter list, with its annotations, defaults and splats removed."""
bound_names(target::Symbol)::Vector{Symbol} = [target]
function bound_names(target::Expr)::Vector{Symbol}
    if target.head === :(::) && length(target.args) == 2
        return bound_names(first(target.args))
    elseif target.head in (:kw, :...)
        return bound_names(first(target.args))
    elseif target.head in (:tuple, :parameters)
        return reduce(vcat, bound_names.(target.args); init = Symbol[])
    end
    return Symbol[]
end
bound_names(::Any)::Vector{Symbol} = Symbol[]

"""The one-letter variable names parsed expression `node` itself binds, besides those `exempt` allows: method parameters, an assignment or loop target, a lambda parameter, a `catch` variable."""
function one_letter_names(node::Expr, exempt::Tuple{Vararg{Symbol}})::Vector{Symbol}
    call = signature_call(node)
    names = Symbol[]
    if !isnothing(call)
        names = reduce(
            vcat,
            bound_names.(call.args[2:end]);
            init = bound_names(first(call.args) isa Symbol ? nothing : first(call.args)),
        )
    elseif node.head === :(=) || node.head === :->
        names = bound_names(first(node.args))
    elseif node.head === :try && length(node.args) >= 3
        names = bound_names(node.args[2])
    end
    return filter(Base.Fix2(is_one_letter, exempt), names)
end

"""One site per one-letter variable name in the Julia file `path`, keyed by file and enclosing function (or testset); `repository.one_letter_exempt` names the allowed ones."""
function one_letter_sites(
        repository::Repository,
        path::AbstractString,
        located::AbstractVector{Located} = located_source(path),
    )::Vector{Site}
    return reduce(vcat, one_letter_item_sites.(path, located, (repository.one_letter_exempt,)); init = Site[])
end

"""One site per `one_letter_names` name `item` of the file `path` binds, at the item's line or its definition's."""
function one_letter_item_sites(path::AbstractString, item::Located, exempt::Tuple{Vararg{Symbol}})::Vector{Site}
    line = item.line
    if !isnothing(signature_call(item.node))
        line = definition_line(item.node, item.line)
    end
    return fill(Site("$(basename(path)) $(item.enclosing)", path, line, ""), length(one_letter_names(item.node, exempt)))
end

# One line of `fatou lint --output concise`: file, line, column, severity, rule and message.
const FATOU_FINDING = r"^(.+?):(\d+):\d+: \w+\[([a-z0-9-]+)\] "
# Fatou's closing line, `checked N file(s): clean` or with a finding count; it is no finding.
const FATOU_SUMMARY = r"^checked \d+ file\(s\)"

"""The `directories` that exist in `repository` (a job's copy holds only `src`, `ext`, `test` and links)."""
present_directories(repository::Repository, directories::Tuple{Vararg{String}})::Tuple{Vararg{String}} =
    filter(isdir ∘ Base.Fix1(joinpath, repository.root), directories)

"""
One site per finding of `fatou lint` over `directories` of `repository`, keyed by file and Fatou
rule and placed at the finding's line (the `fatou` rule's opt-out comment takes it out). Fatou must be
installed; a run that prints a line it did not mean as a finding (a parse error) throws.
"""
function fatou_sites(repository::Repository, directories::Tuple{Vararg{String}})::Vector{
        Site,
    }
    fatou = Sys.which("fatou")
    if isnothing(fatou)
        error("fatou is not on PATH; the fatou rule runs `fatou lint`")
    end
    command = Cmd(
        `$fatou lint --color never --output concise $(collect(directories))`;
        dir = repository.root,
    )
    printed = IOBuffer()
    run(pipeline(ignorestatus(command); stdout = printed, stderr = printed))
    lines = split(String(take!(printed)), '\n'; keepempty = false)
    findings = match.(FATOU_FINDING, lines)
    unread = lines[isnothing.(findings) .& .!occursin.(FATOU_SUMMARY, lines)]
    if !isempty(unread)
        error("fatou lint printed lines that are no finding:\n" * join(unread, "\n"))
    end
    return fatou_site.(repository.root, filter(!isnothing, findings))
end

"""The site of `found`, a `FATOU_FINDING` match, in the repository at `root`."""
fatou_site(root::AbstractString, found::RegexMatch)::Site = Site("$(found[1]) $(found[3])", joinpath(root, found[1]), parse(Int, found[2]), "")

"""One `Site` from `duplicate`, an item of a `jscpd --absolute` JSON report on `repository`."""
function jscpd_site(repository::Repository, duplicate::AbstractDict)::Site
    first_file = string(duplicate["firstFile"]["name"])
    second_file = string(duplicate["secondFile"]["name"])
    rel_first = relpath(first_file, repository.root)
    rel_second = relpath(second_file, repository.root)
    start_line = Int(duplicate["secondFile"]["start"])
    end_line = Int(duplicate["secondFile"]["end"])
    return Site("$rel_second $rel_first", second_file, start_line, end_line, "")
end

"""The `Cmd` running `jscpd` against `dirs` with report written to `report_dir`."""
function jscpd_command(
        jscpd::AbstractString,
        repository::Repository,
        dirs::AbstractVector{String},
        report_dir::AbstractString,
    )::Cmd
    ignore = String[]
    if !isempty(repository.skipped_directories)
        ignore = String["--ignore", join(["**/$d/**" for d in repository.skipped_directories], ",")]
    end
    return Cmd(
        `$jscpd --mode mild --min-lines 5 --min-tokens 50 --silent --no-tips --absolute --reporters json --output $report_dir $ignore $dirs`;
        dir = repository.root,
    )
end

"""
One site per duplicate code block found by `jscpd` over `directories` of `repository`, keyed by
the duplicate file and the duplicated file, placed at the duplicate block's lines. `jscpd` must be
installed and on PATH; an execution failure throws.
"""
function jscpd_sites( # lint: abstract-local  JSON report tables are untyped
        repository::Repository,
        directories::Tuple{Vararg{String}},
    )::Vector{Site}
    jscpd = Sys.which("jscpd")
    if isnothing(jscpd)
        error("jscpd is not on PATH; the jscpd rule runs `jscpd`")
    end
    dirs = present_directories(repository, directories)
    if isempty(dirs)
        return Site[]
    end
    report_dir = mktempdir()
    try
        command = jscpd_command(jscpd, repository, collect(dirs), report_dir)
        printed = IOBuffer()
        run(pipeline(ignorestatus(command); stdout = printed, stderr = printed))
        report_file = joinpath(report_dir, "jscpd-report.json")
        if !isfile(report_file)
            unread = String(take!(printed))
            error("jscpd produced no report:\n$unread")
        end
        json = Base.require(@__MODULE__, :JSON)
        report = Base.invokelatest(json.parsefile, report_file; dicttype = Dict{String, Any})
        duplicates = report["duplicates"]
        return jscpd_site.((repository,), duplicates)
    finally
        rm(report_dir; recursive = true, force = true)
    end
end

"""A `Site` keyed `name` at the declaration of struct `name`."""
function struct_site(name::Symbol, locations::Dict{Symbol, Tuple{String, Int}})::Site
    file, line = get(locations, name, ("", 0))
    return Site(string(name), file, line, "")
end

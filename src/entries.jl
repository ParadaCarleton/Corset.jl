"""
Entry signatures of a loaded module: concrete call signatures such as `Tuple{typeof(f), Int}` that a
type-inference walk can start from. Each source is one function of a `Module` and paths;
`entry_signatures` takes the union of the sources it names.
"""
module Entries

export entry_signatures

"""The sources `source_signatures` and `entry_signatures` accept."""
const SOURCES = (:compiled, :declared, :tests)

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

"""
    compiled_signatures(mod)

The concrete signatures the running process has specialized `mod`'s methods on: those a package
image's precompile workload compiled, and those compiled since loading.
"""
compiled_signatures(mod::Module)::Vector{Type} = unique(
    Type[
        instance.specTypes
            for method in defined_methods(mod)
            for instance in Base.specializations(method)
            if Base.isdispatchtuple(instance.specTypes)
    ],
)

"""
    declared_signatures(mod)

The signatures of `mod`'s methods whose declared argument types are all concrete already.
"""
declared_signatures(mod::Module)::Vector{Type} = Type[method.sig for method in defined_methods(mod) if Base.isdispatchtuple(method.sig)]

"""
    test_trace(root, output; unset = ())

Run the tests of the package at `root` (`Pkg.test`) in a child process started with
`--trace-compile`, writing its output to `output`, and return the trace file's path. The child
inherits every environment variable except those named in `unset`. A failing test run throws.
"""
function test_trace(root::AbstractString, output::IO; unset::Tuple{Vararg{String}} = ())::String
    trace = tempname()
    environment = Dict{String, String}(name => setting for (name, setting) in ENV if !(name in unset))
    command = `$(Base.julia_cmd()) --startup-file=no --project=$root -e "import Pkg; Pkg.test(; julia_args = ARGS)" -- --trace-compile=$trace`
    if !success(pipeline(setenv(ignorestatus(command), environment); stdout = output, stderr = output))
        error("the tests at $root failed; fix them, or drop `tests` from the entry sources")
    end
    return trace
end

"""
    trace_signatures(mod, trace)

The signatures in the `precompile(Tuple{...})` lines of the `--trace-compile` file `trace` that
select a method `mod` defines. A line whose type does not evaluate in this process (a type the
test files define) is dropped.
"""
function trace_signatures(mod::Module, trace::AbstractString)::Vector{Type}
    scope = trace_scope(mod)
    return unique(Type[signature for signature in traced_type.((scope,), readlines(trace)) if defines(mod, signature)])
end

"""A module that binds every loaded package by name, and `mod`, so a trace line's qualified type names resolve."""
function trace_scope(mod::Module)::Module
    scope = Module(:TraceScope)
    loaded = Dict{Symbol, Module}(nameof(package) => package for package in values(Base.loaded_modules)) # lint: hidden-input  a trace names the loaded packages' types
    for (name, package) in merge(loaded, Dict(nameof(mod) => mod))
        if !isdefined(scope, name)
            Core.eval(scope, Expr(:const, Expr(:(=), name, package)))
        end
    end
    return scope
end

"""The type of the trace line `line`, `precompile(Tuple{...})`, evaluated in `scope`; `nothing` for any other line or one that fails to evaluate."""
function traced_type(scope::Module, line::AbstractString)::Any # lint: abstract-local  a trace line evaluates to a value of unknown type
    call = Meta.parse(line; raise = false)
    if !(Meta.isexpr(call, :call, 2) && call.args[1] === :precompile && Meta.isexpr(call.args[2], :curly))
        return nothing
    end
    try
        return Core.eval(scope, call.args[2])
    catch failure
        if failure isa InterruptException
            rethrow()
        end
        return nothing
    end
end

"""Whether `signature` is a concrete call signature that selects a method `mod` defines."""
function defines(mod::Module, signature::Any)::Bool
    if !(signature isa Type && signature <: Tuple && Base.isdispatchtuple(signature))
        return false
    end
    matches = Base._methods_by_ftype(signature, -1, Base.get_world_counter())
    return matches isa AbstractVector && any(match.method.module === mod for match in matches)
end

"""
    configured_signatures(path, name)

The signatures the function `name` of the file `path` returns. The file is included in a fresh
module; the function takes no arguments and returns a vector of signature types. Any other result throws.
"""
function configured_signatures(path::AbstractString, name::Symbol)::Vector{Type}
    holder = Module(:EntryPoints)
    Base.include(holder, path)
    signatures = Base.invokelatest(getfield(holder, name))
    if !(signatures isa AbstractVector && all(Base.Fix2(isa, Type), signatures))
        error("$name in $path returned a $(typeof(signatures)); it must return a vector of signature types")
    end
    return Type[signatures...]
end

"""
    source_signatures(mod, source; root = nothing, output = devnull, unset = ())

The entry signatures of `mod` from one of `SOURCES`: `:compiled` (`compiled_signatures`),
`:declared` (`declared_signatures`) or `:tests` (the `trace_signatures` of the package at `root`'s
`test_trace`, its test output written to `output`, the variables `unset` removed from its environment).
"""
function source_signatures(
        mod::Module,
        source::Symbol;
        root::Union{Nothing, AbstractString} = nothing,
        output::IO = devnull,
        unset::Tuple{Vararg{String}} = (),
    )::Vector{Type}
    if source === :compiled
        return compiled_signatures(mod)
    elseif source === :declared
        return declared_signatures(mod)
    elseif source === :tests
        if isnothing(root)
            throw(ArgumentError("the :tests source runs the package's tests and needs its root"))
        end
        return trace_signatures(mod, test_trace(root, output; unset))
    end
    throw(ArgumentError("no entry source $(repr(source)); the sources are $(join(repr.(SOURCES), ", "))"))
end

"""
    entry_signatures(mod; sources = (:compiled, :declared), root = nothing, output = devnull, unset = ())

The union of the `source_signatures` of `mod` from each of `sources`, each signature once.
"""
function entry_signatures(
        mod::Module;
        sources::Union{Tuple{Vararg{Symbol}}, AbstractVector{Symbol}} = (:compiled, :declared),
        root::Union{Nothing, AbstractString} = nothing,
        output::IO = devnull,
        unset::Tuple{Vararg{String}} = (),
    )::Vector{Type}
    return unique(reduce(vcat, [source_signatures(mod, source; root, output, unset) for source in sources]; init = Type[]))
end

end

# Run-time dispatches and widened results in the frames an entry walk compiles, read from each
# frame's optimized IR. A frame is audited when its method is in the repository's own files.

"""
    logging_call(statement)

Whether a `:call` statement is a logging macro's hand-off to the current logger, which is an
`AbstractLogger` chosen at runtime and so always dispatches.
"""
logging_call(statement::Expr)::Bool = any(logging_argument, statement.args)

"""Whether a call argument names `Base.CoreLogging` or its `handle_message`."""
logging_argument(argument::Any)::Bool =
    argument isa GlobalRef && argument.mod === Base.CoreLogging || argument === Base.CoreLogging.handle_message

"""
Whether `statement` of `ir` dispatches at run time: a `:call` of a generic function, or of a builtin
that calls one (`CALLING_BUILTINS`). A logging hand-off (`logging_call`) dispatches by design.
"""
function dispatches(statement::Expr, ir::COMPILER.IRCode)::Bool
    if statement.head !== :call || logging_call(statement)
        return false
    end
    builtin = called_builtin(statement, ir)
    return isnothing(builtin) || builtin in CALLING_BUILTINS
end
dispatches(::Any, ::COMPILER.IRCode)::Bool = false

"""
    compiled_concretely(return_type)

Whether a caller compiles against `return_type`: concrete, `Union{}` (always throws), a `Type{X}`
constant, a union of at most `UNION_SPLIT_LIMIT` concrete members, which Julia splits, or a
fixed-length tuple whose members each compile concretely.
"""
function compiled_concretely(return_type::Any)::Bool # lint: abstract-local  reflects on types of unknown kind
    if return_type === Union{} || isconcretetype(return_type)
        return true
    elseif return_type <: Type && !(return_type isa Union || return_type isa UnionAll)
        return true # `Type{X}`: a `DataType` before Julia 1.14, a `TypeEq` after
    elseif return_type isa DataType && return_type <: Tuple && !Base.isvatuple(return_type)
        return all(compiled_concretely, return_type.parameters)
    end
    members = Base.uniontypes(return_type)
    return return_type isa Union && length(members) <= UNION_SPLIT_LIMIT && all(isconcretetype, members)
end

"""
The `inferred` frames whose method is in `repository`'s own files and whose first line carries no
`# lint: rule` opt-out, which so covers the whole method.
"""
function audited_frames(repository::Repository, inferred::AbstractVector{Inferred}, rule::AbstractString)::Vector{Inferred}
    own = inferred[startswith.([string(item.method.file) for item in inferred], repository.root)]
    files = unique([string(item.method.file) for item in own])
    return own[.!opted_out.(own, (Dict(files .=> opt_outs.(files, rule)),))]
end

"""Whether the first line of `item`'s method is among the opted-out lines `skipped` holds for its file."""
opted_out(item::Inferred, skipped::AbstractDict{String, OptOuts})::Bool = item.method.line in skipped[string(item.method.file)].lines

"""
    runtime_dispatches(repository, inferred)

Each call the compiler leaves to run-time dispatch (`dispatches`) in a frame of `inferred` that
`audited_frames` keeps, one site per method and source line.
"""
runtime_dispatches(repository::Repository, inferred::AbstractVector{Inferred})::Vector{Site} =
    one_per_line(reduce(vcat, dispatch_sites.(audited_frames(repository, inferred, "runtime-dispatch")); init = Site[]))

"""The `runtime_dispatches` sites of `item`, one per dispatching statement, placed at its line in the method."""
function dispatch_sites(item::Inferred)::Vector{Site}
    indices = findall(dispatches.(item.ir.stmts.stmt, (item.ir,)))
    details = "dispatches " .* string.(first.(getfield.(item.ir.stmts.stmt[indices], :args)))
    return Site.(method_key(item.method), string(item.method.file), statement_line.((item.ir,), (item.method,), indices), details)
end

"""
    widened_returns(repository, inferred)

Each method of `inferred` (as `audited_frames` keeps them) whose inferred result does not compile
concretely (`compiled_concretely`), one site at its first line however many specializations ran.
"""
function widened_returns(repository::Repository, inferred::AbstractVector{Inferred})::Vector{Site}
    widened = [item for item in audited_frames(repository, inferred, "widened-return") if !compiled_concretely(item.code.rettype)]
    return one_per_line(Site[Site(method_key(item.method), string(item.method.file), item.method.line, "returns $(item.code.rettype)") for item in widened])
end

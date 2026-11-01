# Writes through an argument by a function whose name has no `!`, read from each frame's optimized
# IR with the compiler's escape analysis. Indices are escape-analysis indices: argument `n` is `n`,
# SSA value `id` is `id + nargs`.

const ESCAPE = COMPILER.EscapeAnalysis

# Builtins that write through their first operand.
const WRITING_BUILTINS = (
    setfield!, Core.setfieldonce!, Core.modifyfield!, Core.swapfield!, Core.replacefield!,
    Core.memoryrefset!, Core.memoryrefmodify!, Core.memoryrefswap!, Core.memoryrefreplace!, Core.memoryrefsetonce!,
)

# Builtins whose result points into their first operand's memory. Escape analysis aliases neither.
const MEMORY_VIEWS = (Core.memoryrefnew, Core.memoryrefget)

# Builtins that call a generic function chosen at run time.
const CALLING_BUILTINS = (Core._apply_iterate, Core.invoke)

"""The escape analysis of `ir`, a method body of `nargs` arguments, in the current world."""
function escape_state(ir::COMPILER.IRCode, nargs::Integer)::ESCAPE.EscapeState
    interpreter = COMPILER.NativeInterpreter()
    return ESCAPE.analyze_escapes(ir, Int(nargs), COMPILER.optimizer_lattice(interpreter), COMPILER.get_escape_cache(interpreter))
end

"""The escape-analysis index of IR operand `operand`; `nothing` for a constant or a global."""
operand_index(operand::Union{Core.Argument, Core.SSAValue}, estate::ESCAPE.EscapeState)::Int = ESCAPE.iridx(operand, estate)
operand_index(::Any, ::ESCAPE.EscapeState)::Nothing = nothing

"""The indices of the IR operands `operands` that escape analysis tracks."""
operand_indices(operands::AbstractVector, estate::ESCAPE.EscapeState)::Vector{Int} =
    Int[index for index in operand_index.(operands, (estate,)) if !isnothing(index)]

"""The indices escape analysis puts in one alias set with `index`, `index` included."""
alias_indices(index::Integer, estate::ESCAPE.EscapeState)::Vector{Int} = something(ESCAPE.getaliases(index, estate), collect(index:index))

"""The builtin or intrinsic a `:call` statement calls; `nothing` for a generic function."""
function called_builtin(statement::Expr, ir::COMPILER.IRCode)::Union{Nothing, Core.Builtin, Core.IntrinsicFunction}
    callee = COMPILER.singleton_type(COMPILER.argextype(first(statement.args), ir))
    if callee isa Union{Core.Builtin, Core.IntrinsicFunction}
        return callee
    end
    return nothing
end

"""The aliases of the memory that SSA index `index` views when its statement is a `MEMORY_VIEWS` call; none otherwise."""
function view_sources(index::Integer, ir::COMPILER.IRCode, estate::ESCAPE.EscapeState)::Vector{Int}
    if index <= estate.nargs
        return Int[]
    end
    statement = ir.stmts.stmt[index - estate.nargs]
    if !(statement isa Expr && statement.head === :call && called_builtin(statement, ir) in MEMORY_VIEWS)
        return Int[]
    end
    return reduce(vcat, alias_indices.(operand_indices(statement.args[2:2], estate), (estate,)); init = Int[])
end

"""
The arguments (2 and up; 1 is the function itself) whose memory the values at `indices` may point
into: their escape-analysis aliases, closed under the memory a `MEMORY_VIEWS` result views.
"""
function reached_arguments(indices::AbstractVector{<:Integer}, ir::COMPILER.IRCode, estate::ESCAPE.EscapeState)::Vector{Int}
    reached = unique(reduce(vcat, alias_indices.(indices, (estate,)); init = Int[]))
    grown = union(reached, reduce(vcat, view_sources.(reached, (ir,), (estate,)); init = Int[]))
    while length(grown) > length(reached)
        reached = grown
        grown = union(reached, reduce(vcat, view_sources.(reached, (ir,), (estate,)); init = Int[]))
    end
    arguments = filter(in(2:estate.nargs), reached)
    return sort!(arguments[writable.(COMPILER.widenconst.(ir.argtypes[arguments]))])
end

# Handles whose writes leave Julia: files, pipes, sockets, terminals and processes.
const OS_HANDLES = Union{
    IOStream, Base.Filesystem.File, Base.DevNull, Core.CoreSTDOUT, Core.CoreSTDERR,
    Base.LibuvServer, Base.Process, Base.ProcessChain, Pipe,
}

"""Whether every value of type `type` is an OS-backed handle: an `OS_HANDLES` type or a libuv stream other than the in-memory `BufferStream`."""
os_handle(type::Type)::Bool = type <: OS_HANDLES || (type <: Base.LibuvStream && !(Base.BufferStream <: type)) || os_context(type)

"""Whether `type` is an `IOContext` around an `os_handle`."""
os_context(type::DataType)::Bool = type <: IOContext && os_handle(only(type.parameters))
os_context(::Type)::Bool = false

"""
Whether a write through a value of type `type` changes a Julia object: not `plain_capture` data, a
type or a module, and not an `os_handle`, whose writes reach the file system or the OS.
"""
writable(type::Type)::Bool = !(plain_capture(type) || type <: Union{Type, Module} || os_handle(type))

"""
What a frame or statement does to arguments, as indices: those it writes through, those it passes to
a runtime dispatch, and those it passes to a `ccall`. The analysis cannot read the last two callees.
"""
struct ArgumentWrites
    written::Vector{Int}
    dispatched::Vector{Int}
    foreign::Vector{Int}
end

const NO_WRITES = ArgumentWrites(Int[], Int[], Int[])

"""
    argument_writes(frame, frames, stack)

The `ArgumentWrites` of `frame`, as argument numbers; a written argument is neither dispatched nor
foreign. A statically resolved callee writes the arguments its own frame in `frames` (keyed by method
instance) writes; a callee named with `!` writes its first argument; any other callee writes none.
`stack` holds the instances being summarized, which a recursive call skips.
"""
function argument_writes(
        frame::Inferred,
        frames::AbstractDict{Core.MethodInstance, Inferred},
        stack::Tuple,
    )::ArgumentWrites
    estate = escape_state(frame.ir, frame.method.nargs)
    effects = statement_writes.(frame.ir.stmts.stmt, (frame.ir,), (estate,), (frames,), (stack,))
    written = effect_arguments(:written, effects, frame.ir, estate)
    dispatched = setdiff(effect_arguments(:dispatched, effects, frame.ir, estate), written)
    return ArgumentWrites(written, dispatched, setdiff(effect_arguments(:foreign, effects, frame.ir, estate), written))
end

"""The arguments that the `field` operands of the statement `effects` reach (`reached_arguments`)."""
effect_arguments(field::Symbol, effects::AbstractVector{ArgumentWrites}, ir::COMPILER.IRCode, estate::ESCAPE.EscapeState)::Vector{Int} =
    reached_arguments(reduce(vcat, getfield.(effects, field); init = Int[]), ir, estate)

"""The `ArgumentWrites` of one IR statement, as the indices of its operands."""
statement_writes(::Any, ::COMPILER.IRCode, ::ESCAPE.EscapeState, ::AbstractDict, ::Tuple)::ArgumentWrites = NO_WRITES

function statement_writes(
        statement::Expr,
        ir::COMPILER.IRCode,
        estate::ESCAPE.EscapeState,
        frames::AbstractDict{Core.MethodInstance, Inferred},
        stack::Tuple,
    )::ArgumentWrites
    if statement.head === :invoke
        return ArgumentWrites(invoked_writes(statement, estate, frames, stack), Int[], Int[])
    elseif statement.head === :foreigncall
        return ArgumentWrites(Int[], Int[], writable_operands(statement.args[6:(5 + length(statement.args[3]))], ir, estate))
    elseif statement.head !== :call
        return NO_WRITES
    end
    builtin = called_builtin(statement, ir)
    if builtin in WRITING_BUILTINS
        return ArgumentWrites(operand_indices(statement.args[2:2], estate), Int[], Int[])
    elseif isnothing(builtin) || builtin in CALLING_BUILTINS
        return ArgumentWrites(Int[], writable_operands(statement.args[2:end], ir, estate), Int[])
    end
    return NO_WRITES
end

"""
The indices of the `operands` whose IR type is `writable`. A call cannot write a `Symbol` or a bits
value (a `Ptr` too, which C reads by value) it is passed.
"""
writable_operands(operands::AbstractVector, ir::COMPILER.IRCode, estate::ESCAPE.EscapeState)::Vector{Int} =
    operand_indices(operands[writable.(COMPILER.widenconst.(COMPILER.argextype.(operands, (ir,))))], estate)

"""The indices of the operands of `:invoke` statement `statement` that its callee writes (`argument_writes`)."""
function invoked_writes(
        statement::Expr,
        estate::ESCAPE.EscapeState,
        frames::AbstractDict{Core.MethodInstance, Inferred},
        stack::Tuple,
    )::Vector{Int}
    instance = invoked_instance(first(statement.args))
    operands = statement.args[2:end]
    if isnothing(instance) || !(instance.def isa Method) || (instance in stack)
        return Int[]
    elseif endswith(string(instance.def.name), "!")
        return operand_indices(operands[2:min(2, end)], estate)
    elseif !haskey(frames, instance)
        return Int[]
    end
    written = argument_writes(frames[instance], frames, (stack..., instance)).written
    return operand_indices(operands[filter(<=(length(operands)), written)], estate)
end

"""
Each `is_unmarked_function` among `inferred` whose frame writes through one of its arguments, one
site per method: "writes argument `x`", or "may write" when the argument reaches a runtime dispatch
(which `runtime-dispatch` also reports) or a `ccall`, whose code the analysis does not read.
"""
function unmarked_mutations(repository::Repository, inferred::AbstractVector{Inferred})::Vector{Site}
    frames = Dict{Core.MethodInstance, Inferred}(item.code.parent => item for item in inferred)
    own = inferred[is_unmarked_function.((repository,), getfield.(inferred, :method))]
    return one_per_line(reduce(vcat, mutation_sites.(own, (frames,)); init = Site[]))
end

"""The `unmarked_mutations` sites of `item`, one per written or unverified argument."""
function mutation_sites(item::Inferred, frames::AbstractDict{Core.MethodInstance, Inferred})::Vector{Site}
    writes = argument_writes(item, frames, (item.code.parent,))
    names = "`" .* string.(item.code.slotnames) .* "`"
    reported = Base.Fix1(filter, !Base.Fix1(declared_io, item.method))
    details = vcat(
        "writes argument " .* names[reported(writes.written)] .* " but its name has no `!`",
        "argument " .* names[reported(writes.dispatched)] .* " reaches a runtime dispatch (`runtime-dispatch`) and may be written",
        "argument " .* names[reported(writes.foreign)] .* " reaches a `ccall` and may be written",
    )
    return Site.(method_key(item.method), string(item.method.file), item.method.line, details)
end

"""
Whether `method` declares argument `index` as an abstract `IO` (`io::IO`, `io::T where T <: IO`): it
writes whatever stream its caller passes, an OS handle included, so a specialization's `IOBuffer` does not count.
"""
function declared_io(method::Method, index::Integer)::Bool # lint: abstract-local  signature parameters are any type
    parameters = collect(Any, Base.unwrap_unionall(method.sig).parameters) # lint: abstract-local  signature parameters are any type
    declared = get(parameters, index, Any)
    if declared isa TypeVar
        declared = declared.ub
    end
    return declared isa Type && declared <: IO && !isconcretetype(declared)
end

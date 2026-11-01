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
a runtime dispatch it cannot resolve, and those it passes to a `ccall`. The analysis cannot read the
last two callees. `writers` pairs a written index with the runtime-dispatch candidate that writes it.
"""
struct ArgumentWrites
    written::Vector{Int}
    dispatched::Vector{Int}
    foreign::Vector{Int}
    writers::Vector{Pair{Int, Method}}
end

ArgumentWrites(written::AbstractVector{Int}, dispatched::AbstractVector{Int}, foreign::AbstractVector{Int})::ArgumentWrites =
    ArgumentWrites(written, dispatched, foreign, Pair{Int, Method}[])

const NO_WRITES = ArgumentWrites(Int[], Int[], Int[])

"""
    argument_writes(frame, frames, stack, search)

The `ArgumentWrites` of `frame`, as argument numbers; a written argument is neither dispatched nor
foreign. A statically resolved callee writes the arguments its own frame in `frames` (keyed by method
instance) writes; a callee named with `!` writes its first argument; any other callee writes none.
A runtime dispatch writes what its `call_candidates` in `search` write (`dispatch_writes`).
`stack` holds the instances being summarized, which a recursive call skips.
"""
function argument_writes(
        frame::Inferred,
        frames::AbstractDict{Core.MethodInstance, Inferred},
        stack::Tuple,
        search::CandidateSearch,
    )::ArgumentWrites
    estate = escape_state(frame.ir, frame.method.nargs)
    effects = statement_writes.(frame.ir.stmts.stmt, (frame.ir,), (estate,), (frames,), (stack,), (search,))
    written = effect_arguments(:written, effects, frame.ir, estate)
    dispatched = setdiff(effect_arguments(:dispatched, effects, frame.ir, estate), written)
    foreign = setdiff(effect_arguments(:foreign, effects, frame.ir, estate), written)
    return ArgumentWrites(written, dispatched, foreign, reduce(vcat, reached_writers.(effects, (frame.ir,), (estate,)); init = Pair{Int, Method}[]))
end

"""The arguments that the `field` operands of the statement `effects` reach (`reached_arguments`)."""
effect_arguments(field::Symbol, effects::AbstractVector{ArgumentWrites}, ir::COMPILER.IRCode, estate::ESCAPE.EscapeState)::Vector{Int} =
    reached_arguments(reduce(vcat, getfield.(effects, field); init = Int[]), ir, estate)

"""The `writers` of statement `effect`, each index replaced by the arguments it reaches."""
reached_writers(effect::ArgumentWrites, ir::COMPILER.IRCode, estate::ESCAPE.EscapeState)::Vector{Pair{Int, Method}} =
    reduce(vcat, writer_arguments.(effect.writers, (ir,), (estate,)); init = Pair{Int, Method}[])

"""The arguments the index of `writer` reaches (`reached_arguments`), each paired with its candidate."""
writer_arguments(writer::Pair{Int, Method}, ir::COMPILER.IRCode, estate::ESCAPE.EscapeState)::Vector{Pair{Int, Method}} =
    reached_arguments([first(writer)], ir, estate) .=> (last(writer),)

"""The `ArgumentWrites` of one IR statement, as the indices of its operands."""
statement_writes(::Any, ::COMPILER.IRCode, ::ESCAPE.EscapeState, ::AbstractDict, ::Tuple, ::CandidateSearch)::ArgumentWrites = NO_WRITES

function statement_writes(
        statement::Expr,
        ir::COMPILER.IRCode,
        estate::ESCAPE.EscapeState,
        frames::AbstractDict{Core.MethodInstance, Inferred},
        stack::Tuple,
        search::CandidateSearch,
    )::ArgumentWrites
    if statement.head === :invoke
        return ArgumentWrites(invoked_writes(statement, estate, frames, stack, search), Int[], Int[])
    elseif statement.head === :foreigncall
        return ArgumentWrites(Int[], Int[], writable_operands(statement.args[6:(5 + length(statement.args[3]))], ir, estate))
    elseif statement.head !== :call
        return NO_WRITES
    end
    builtin = called_builtin(statement, ir)
    if builtin in WRITING_BUILTINS
        return ArgumentWrites(operand_indices(statement.args[2:2], estate), Int[], Int[])
    elseif isnothing(builtin) || builtin in CALLING_BUILTINS
        return dispatch_writes(statement, ir, estate, frames, stack, search)
    end
    return NO_WRITES
end

"""
The `ArgumentWrites` of runtime-dispatch `statement`, read from its `call_candidates`. An operand a
candidate writes is written, and names that candidate. An operand stays dispatched (unresolved) when
the candidates are incomplete, one is on `stack`, or one passes it on to a dispatch or a `ccall`.
"""
function dispatch_writes(
        statement::Expr,
        ir::COMPILER.IRCode,
        estate::ESCAPE.EscapeState,
        frames::AbstractDict{Core.MethodInstance, Inferred},
        stack::Tuple,
        search::CandidateSearch,
    )::ArgumentWrites
    positions = writable_positions(statement.args, ir)
    candidates = call_candidates(statement, ir, search)
    if !candidates.complete || any(in(stack), getfield.(getfield.(candidates.frames, :code), :parent))
        return ArgumentWrites(Int[], operand_indices(statement.args[positions], estate), Int[])
    end
    # A candidate's own dispatches stay unresolved: the budget covers one level.
    effects = candidate_writes.(candidates.frames, (frames,), (stack,), (with_limit(search, 0),))
    writers = reduce(vcat, position_writers.(candidates.frames, effects, (positions,), (statement.args,), (estate,)); init = Pair{Int, Method}[])
    unresolved = unique(reduce(vcat, unresolved_positions.(candidates.frames, effects, (positions,)); init = Int[]))
    return ArgumentWrites(unique(first.(writers)), operand_indices(statement.args[unresolved], estate), Int[], writers)
end

"""The `ArgumentWrites` of candidate `frame`, summarized with `frame` pushed on `stack`."""
candidate_writes(frame::Inferred, frames::AbstractDict{Core.MethodInstance, Inferred}, stack::Tuple, search::CandidateSearch)::ArgumentWrites =
    argument_writes(frame, frames, (stack..., frame.code.parent), search)

"""The operand indices at `positions` of call `operands` that candidate `frame` writes (`effect`), each paired with its method."""
function position_writers(
        frame::Inferred,
        effect::ArgumentWrites,
        positions::AbstractVector{Int},
        operands::AbstractVector,
        estate::ESCAPE.EscapeState,
    )::Vector{Pair{Int, Method}}
    written = positions[in.(candidate_argument.((frame.method,), positions), (effect.written,))]
    return operand_indices(operands[written], estate) .=> (frame.method,)
end

"""The `positions` whose argument candidate `frame` passes on to a dispatch or a `ccall` (`effect`)."""
unresolved_positions(frame::Inferred, effect::ArgumentWrites, positions::AbstractVector{Int})::Vector{Int} =
    positions[in.(candidate_argument.((frame.method,), positions), (vcat(effect.dispatched, effect.foreign),))]

"""The positions (2 and up) of `operands`, a call's arguments with its callee first, whose IR type is `writable`."""
function writable_positions(operands::AbstractVector, ir::COMPILER.IRCode)::Vector{Int}
    positions = collect(2:length(operands))
    return positions[writable.(COMPILER.widenconst.(COMPILER.argextype.(operands[positions], (ir,))))]
end

"""The argument of `method` that call operand `position` binds: a varargs method gathers the trailing operands into its last."""
function candidate_argument(method::Method, position::Integer)::Int
    if method.isva
        return min(position, Int(method.nargs))
    end
    return position
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
        search::CandidateSearch,
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
    written = argument_writes(frames[instance], frames, (stack..., instance), search).written
    return operand_indices(operands[filter(<=(length(operands)), written)], estate)
end

"""
    unmarked_mutations(repository, inferred; search = CandidateSearch(inferred))

Each `is_unmarked_method` among `inferred` whose frame writes through one of its arguments, one
site per method: "writes argument `x`", or "may write" when the argument reaches a `ccall` or a
runtime dispatch whose `call_candidates` in `search` are incomplete. `runtime-dispatch` reports
the dispatch itself. A write by a runtime-dispatch candidate names the candidate. A writing method
added to another module's function (`Base.length`, `Base.iterate`) breaks what its callers expect.
"""
function unmarked_mutations(
        repository::Repository,
        inferred::AbstractVector{Inferred};
        search::CandidateSearch = CandidateSearch(inferred),
    )::Vector{Site}
    frames = Dict{Core.MethodInstance, Inferred}(item.code.parent => item for item in inferred)
    own = inferred[is_unmarked_method.((repository,), getfield.(inferred, :method))]
    return one_per_line(reduce(vcat, mutation_sites.(own, (frames,), (search,)); init = Site[]))
end

"""The `unmarked_mutations` sites of `item`, one per written or unverified argument."""
function mutation_sites(item::Inferred, frames::AbstractDict{Core.MethodInstance, Inferred}, search::CandidateSearch)::Vector{Site}
    writes = argument_writes(item, frames, (item.code.parent,), search)
    names = "`" .* string.(item.code.slotnames) .* "`"
    reported = Base.Fix1(filter, !Base.Fix1(declared_io, item.method))
    written = reported(writes.written)
    details = vcat(
        written_detail.(names[written], (item.method,)) .* writer_note.(written, (writes.writers,)),
        "argument " .* names[reported(writes.dispatched)] .* " reaches a runtime dispatch (`runtime-dispatch`) and may be written",
        "argument " .* names[reported(writes.foreign)] .* " reaches a `ccall` and may be written",
    )
    return Site.(method_key(item.method), string(item.method.file), item.method.line, details)
end

"""The note naming the runtime-dispatch candidates that write `argument`, among `writers`; empty when none does."""
function writer_note(argument::Integer, writers::AbstractVector{Pair{Int, Method}})::String
    methods_ = unique(last.(writers[first.(writers) .== argument]))
    if isempty(methods_)
        return ""
    end
    return " (runtime-dispatch candidate " * join("`" .* candidate_name.(methods_) .* "`", ", ") * " writes it)"
end

"""The detail of a site where `method` writes its argument `name`, naming the owner of a function another module owns."""
function written_detail(name::AbstractString, method::Method)::String
    owner = function_owner(method)
    if owner === method.module
        return "writes argument $name but its name has no `!`"
    end
    return "adds a writing method to `$owner.$(method.name)`, which callers expect not to write: it writes argument $name"
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

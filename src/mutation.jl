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

"""
Whether a write through a value of type `type` counts: not `plain_capture` data, a type or a module,
and not an `IO` or a lock, whose functions (`show`, `read`, `lock`) write them without a `!` by convention.
"""
writable(type::Type)::Bool = !(plain_capture(type) || type <: Union{Type, Module, IO, Base.AbstractLock})

"""What a frame or statement does to arguments: the indices it writes through, and those it passes to a call the analysis cannot follow."""
struct ArgumentWrites
    written::Vector{Int}
    unverified::Vector{Int}
end

const NO_WRITES = ArgumentWrites(Int[], Int[])

"""
    argument_writes(frame, frames, stack)

The `ArgumentWrites` of `frame`, as argument numbers. A statically resolved callee writes the
arguments its own frame in `frames` (keyed by method instance) writes; a callee named with `!` writes
its first argument; any other callee writes none. `stack` holds the instances being summarized,
which a recursive call skips.
"""
function argument_writes(
        frame::Inferred,
        frames::AbstractDict{Core.MethodInstance, Inferred},
        stack::Tuple,
    )::ArgumentWrites
    estate = escape_state(frame.ir, frame.method.nargs)
    effects = statement_writes.(frame.ir.stmts.stmt, (frame.ir,), (estate,), (frames,), (stack,))
    written = reached_arguments(reduce(vcat, getfield.(effects, :written); init = Int[]), frame.ir, estate)
    unverified = reached_arguments(reduce(vcat, getfield.(effects, :unverified); init = Int[]), frame.ir, estate)
    return ArgumentWrites(written, setdiff(unverified, written))
end

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
        return ArgumentWrites(invoked_writes(statement, estate, frames, stack), Int[])
    elseif statement.head === :foreigncall
        return ArgumentWrites(Int[], writable_operands(statement.args[6:(5 + length(statement.args[3]))], ir, estate))
    elseif statement.head !== :call
        return NO_WRITES
    end
    builtin = called_builtin(statement, ir)
    if builtin in WRITING_BUILTINS
        return ArgumentWrites(operand_indices(statement.args[2:2], estate), Int[])
    elseif isnothing(builtin) || builtin in CALLING_BUILTINS
        return ArgumentWrites(Int[], writable_operands(statement.args[2:end], ir, estate))
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
site per method: "writes argument `x`", or "passes argument `x` to a call the analysis cannot follow"
when the argument reaches a dynamic dispatch or a `ccall`, whose code the analysis does not read.
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
    details = vcat(
        "writes argument " .* names[writes.written] .* " but its name has no `!`",
        "passes argument " .* names[writes.unverified] .* " to a call the analysis cannot follow",
    )
    return Site.(method_key(item.method), string(item.method.file), item.method.line, details)
end

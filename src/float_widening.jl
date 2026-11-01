# Statements whose float result is wider than every float their method receives, read from each
# audited frame's optimized IR. A runtime dispatch is judged by its `call_candidates`.

"""
The concrete float types `type` holds: itself, or any type parameter at depth below 5
(`Vector{Float32}`, `Complex{Float64}`, `Tuple{Int, Float16}`), each union member included.
"""
function held_floats(type::Any, depth::Integer)::Vector{DataType} # lint: abstract-local  reflects on types of unknown kind
    if depth > 4
        return DataType[]
    elseif type isa Union
        return union(held_floats(type.a, depth + 1), held_floats(type.b, depth + 1))
    elseif !(type isa DataType)
        return DataType[]
    elseif type <: AbstractFloat && isconcretetype(type)
        return DataType[type]
    end
    return unique(reduce(vcat, held_floats.(collect(type.parameters), depth + 1); init = DataType[]))
end

"""The floats a value of IR type `type` holds; a `Type{Float64}` value holds no float."""
value_floats(type::Type)::Vector{DataType} = ifelse(type <: Type, DataType[], held_floats(type, 0))

"""The widest of `floats`, by precision; `floats` holds at least one."""
widest(floats::AbstractVector{DataType})::DataType = floats[argmax(precision.(floats))]

"""
A frame's float budget: the floats its arguments hold, and the precision (bits) of the widest. A
statement whose result holds a float of more precision widens.
"""
struct FloatBudget
    floats::Vector{DataType}
    bits::Int
end

"""The `FloatBudget` of `item`, from its argument types."""
function float_budget(item::Inferred)::FloatBudget
    floats = unique(reduce(vcat, held_floats.(COMPILER.widenconst.(item.ir.argtypes[2:item.method.nargs]), 0); init = DataType[]))
    return FloatBudget(floats, maximum(precision, floats; init = 0))
end

"""Whether a frame of `budget` is judged: it receives a float, and none as wide as `Float64`."""
judged(budget::FloatBudget)::Bool = 0 < budget.bits < precision(Float64) # lint: float64  the rule measures against Float64

"""Whether `floats` hold one wider than `budget` allows."""
wider(floats::AbstractVector{DataType}, budget::FloatBudget)::Bool = maximum(precision, floats; init = 0) > budget.bits

"""
One IR operand as the rule reads it: whether the frame computed it (an argument or SSA value, which
widens nothing itself), the floats it brings in, and how a detail names it.
"""
struct Operand
    computed::Bool
    floats::Vector{DataType}
    label::String
end

"""How a detail names IR value `operand`. Julia 1.14 keeps a global as a `Core.BindingPartition`, named by its binding."""
ir_label(operand::Any)::String = string(operand) # lint: abstract-local  IR operands are any value
@static if isdefined(Base, :partition_owner)
    ir_label(operand::Core.BindingPartition)::String = string(Base.partition_owner(operand).globalref) # lint: non-public-access  1.14 only # COV_EXCL_LINE
end

"""The `Operand` of IR value `operand` in `ir`. A type operand (`Float64` in `sitofp(Float64, n)`) brings in its own float."""
function Operand(operand::Any, ir::COMPILER.IRCode)::Operand # lint: abstract-local  IR operands are any value
    extended = COMPILER.argextype(operand, ir)
    floats = value_floats(COMPILER.widenconst(extended))
    # Read a type operand from its constant: Julia 1.14 widens `Const(Float64)` to `Core.TypeEgal{Float64}`.
    if extended isa Core.Const && extended.val isa DataType
        floats = held_floats(extended.val, 0)
    end
    return Operand(operand isa Union{Core.Argument, Core.SSAValue}, floats, ir_label(operand))
end

"""
The `Operand`s of IR statement `statement`: an `Expr`'s arguments past an `:invoke`'s instance, a φ's
values, a π's or a `return`'s value, a global read itself.
"""
statement_operands(statement::Expr, ir::COMPILER.IRCode)::Vector{Operand} = Operand.(statement.args[(1 + (statement.head === :invoke)):end], (ir,))
statement_operands(statement::Core.PhiNode, ir::COMPILER.IRCode)::Vector{Operand} =
    Operand.(statement.values[isassigned.((statement.values,), eachindex(statement.values))], (ir,))
statement_operands(statement::Core.PiNode, ir::COMPILER.IRCode)::Vector{Operand} = [Operand(statement.val, ir)]
statement_operands(statement::Union{GlobalRef, Core.BindingPartition}, ir::COMPILER.IRCode)::Vector{Operand} = [Operand(statement, ir)]
statement_operands(statement::Core.ReturnNode, ir::COMPILER.IRCode)::Vector{Operand} = returned_operands(statement, ir)
statement_operands(::Any, ::COMPILER.IRCode)::Vector{Operand} = Operand[]

"""The `Operand` a `return` returns: none for an unreachable one."""
function returned_operands(statement::Core.ReturnNode, ir::COMPILER.IRCode)::Vector{Operand}
    if !isdefined(statement, :val)
        return Operand[]
    end
    return [Operand(statement.val, ir)]
end

"""The floats IR statement `statement` makes: those of its inferred `type`, or a `return`'s value's (its `operands`)."""
result_floats(::Any, type::Any, ::AbstractVector{Operand})::Vector{DataType} = value_floats(COMPILER.widenconst(type)) # lint: abstract-local  IR statements and types are any value
result_floats(::Core.ReturnNode, ::Any, operands::AbstractVector{Operand})::Vector{DataType} = reduce(vcat, getfield.(operands, :floats); init = DataType[])

"""
The detail of IR statement `statement`, of inferred type `type`, when it widens: its result holds a
float wider than `budget` and no computed operand already did. It names the first operand that brings
the wide float in, else the callee; `nothing` when the statement does not widen.
"""
function widening_detail(statement::Any, type::Any, ir::COMPILER.IRCode, budget::FloatBudget)::Union{Nothing, String} # lint: abstract-local  IR statements and types are any value
    operands = statement_operands(statement, ir)
    result = result_floats(statement, type, operands)
    wide = operands[wider.(getfield.(operands, :floats), (budget,))]
    if !wider(result, budget) || any(getfield.(wide, :computed))
        return nothing
    end
    return "$(widening_source(statement, wide)) makes a $(widest(result)); the widest float argument is $(widest(budget.floats))"
end

"""How a widening detail names its source: the first of the `wide` operands, else the callee of `statement`."""
function widening_source(statement::Any, wide::AbstractVector{Operand})::String # lint: abstract-local  IR statements are any value
    if !isempty(wide)
        return "`$(first(wide).label)`"
    end
    return "`$(callee_label(statement))`"
end

"""
The callee an IR call statement names: an `:invoke`'s method, else its first argument. Another
statement is named by its type.
"""
callee_label(statement::Any)::String = string(typeof(statement)) # lint: abstract-local  IR statements are any value

function callee_label(statement::Expr)::String
    instance = invoked_instance(first(statement.args))
    if !isnothing(instance)
        return string(instance.def.name)
    end
    return ir_label(first(statement.args))
end

"""
The detail of runtime-dispatch `statement` of `ir` under `budget`: a candidate whose result holds a
wider float makes it definite; an incomplete list makes it "may widen". A dispatch whose operand types
hold none of the floats `budget` receives is skipped (`nothing`).
"""
function dispatch_widening(statement::Expr, ir::COMPILER.IRCode, budget::FloatBudget, search::CandidateSearch)::Union{Nothing, String}
    if !any(carries_floats.(COMPILER.widenconst.(COMPILER.argextype.(statement.args[2:end], (ir,))), (budget,)))
        return nothing
    end
    candidates = call_candidates(statement, ir, search)
    returned = value_floats.(COMPILER.widenconst.(getfield.(getfield.(candidates.frames, :code), :rettype)))
    wide = getfield.(candidates.frames[wider.(returned, (budget,))], :method)
    callee = ir_label(first(statement.args))
    if !isempty(wide)
        return "dispatches `$callee`; candidate " * join("`" .* candidate_name.(wide) .* "`", ", ") * " returns a float wider than $(widest(budget.floats))"
    elseif !candidates.complete
        return "dispatches `$callee` on a $(widest(budget.floats)) and may widen (`runtime-dispatch`)"
    end
    return nothing
end

"""Whether a value of type `type` may hold a float of `budget`: it may be one, or holds one in a parameter."""
carries_floats(type::Type, budget::FloatBudget)::Bool =
    typeintersect(type, Union{budget.floats...}) !== Union{} || !isempty(intersect(held_floats(type, 0), budget.floats))

"""
    float_widenings(repository, inferred; search = CandidateSearch(inferred))

Each statement of an audited frame (`audited_frames`) whose float result is wider than every float its
method receives in its arguments (`x::Float32 * 2.0`, `float(n)` in a `Float32` method), one site per
method and line. A frame with no float argument, or one as wide as `Float64`, is skipped. A runtime
dispatch is judged by its `call_candidates` in `search` (`dispatch_widening`).
"""
function float_widenings(
        repository::Repository,
        inferred::AbstractVector{Inferred};
        search::CandidateSearch = CandidateSearch(inferred),
    )::Vector{Site}
    return one_per_line(reduce(vcat, frame_widenings.(audited_frames(repository, inferred, "float-widening"), (search,)); init = Site[]))
end

"""The `float_widenings` sites of `item`, one per widening statement."""
function frame_widenings(item::Inferred, search::CandidateSearch)::Vector{Site}
    budget = float_budget(item)
    if !judged(budget)
        return Site[]
    end
    details = statement_widening.(item.ir.stmts.stmt, item.ir.stmts.type, (item.ir,), (budget,), (search,))
    found = findall(!isnothing, details)
    return Site.(method_key(item.method), string(item.method.file), statement_line.((item.ir,), (item.method,), found), details[found])
end

"""The widening detail of IR statement `statement` of type `type`: a dispatch's (`dispatch_widening`) or another's (`widening_detail`)."""
function statement_widening(statement::Any, type::Any, ir::COMPILER.IRCode, budget::FloatBudget, search::CandidateSearch)::Union{Nothing, String} # lint: abstract-local  IR statements and types are any value
    if dispatches(statement, ir)
        return dispatch_widening(statement, ir, budget, search)
    end
    return widening_detail(statement, type, ir, budget)
end

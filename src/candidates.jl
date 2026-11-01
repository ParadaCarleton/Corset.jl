# The methods a runtime-dispatch call may reach, listed from the call's abstract signature and
# inferred once each. A count budget bounds the list, so a run's answer depends on the code alone.

"""The `candidate_limit` a search uses unless told otherwise: the most methods one runtime-dispatch site lists."""
const DEFAULT_CANDIDATE_LIMIT = 4

"""
A candidate search: at most `limit` methods per runtime-dispatch call (0 lists none), and every frame
inferred so far by method instance, `nothing` where inference failed. Searches that share `frames`
infer no frame twice.
"""
struct CandidateSearch
    limit::Int
    frames::Dict{Core.MethodInstance, Union{Nothing, Inferred}}
end

"""
    CandidateSearch(inferred; candidate_limit = DEFAULT_CANDIDATE_LIMIT)

A search seeded with the rules' own `inferred` frames. A negative `candidate_limit` throws.
"""
function CandidateSearch(inferred::AbstractVector{Inferred}; candidate_limit::Integer = DEFAULT_CANDIDATE_LIMIT)::CandidateSearch
    if candidate_limit < 0
        throw(ArgumentError("candidate_limit is $candidate_limit; pass 0 to list no candidates, or a positive count"))
    end
    seeded = Dict{Core.MethodInstance, Union{Nothing, Inferred}}(item.code.parent => item for item in inferred)
    return CandidateSearch(candidate_limit, seeded)
end

"""The same search, sharing `search`'s frames, with the budget `limit`."""
with_limit(search::CandidateSearch, limit::Integer)::CandidateSearch = CandidateSearch(limit, search.frames)

"""
The methods a runtime-dispatch call may reach, each inferred over its intersection with the call's
signature. `complete` is false when the budget ran out, the call has no plain signature (a splat, a
`Core.invoke`), or inference failed on a candidate; `frames` then holds the candidates it did type.
"""
struct Candidates
    frames::Vector{Inferred}
    complete::Bool
end

const NO_CANDIDATES = Candidates(Inferred[], false)

"""The abstract signature of `:call` statement `statement` from its inferred operand types; `nothing` for a builtin's call."""
function call_signature(statement::Expr, ir::COMPILER.IRCode)::Union{Nothing, Type}
    if !isnothing(called_builtin(statement, ir))
        return nothing
    end
    return Tuple{COMPILER.widenconst.(COMPILER.argextype.(statement.args, (ir,)))...}
end

"""
    call_candidates(statement, ir, search)

The `Candidates` of the runtime-dispatch `statement` of `ir`: none and incomplete past `search.limit` methods.
"""
function call_candidates(statement::Expr, ir::COMPILER.IRCode, search::CandidateSearch)::Candidates # lint: unmarked-mutation  memoizes frames in the search
    signature = call_signature(statement, ir)
    if search.limit == 0 || isnothing(signature)
        return NO_CANDIDATES
    end
    matches = Base._methods_by_ftype(signature, search.limit, Base.get_world_counter())
    if !(matches isa AbstractVector)
        return NO_CANDIDATES
    end
    frames = candidate_frame.((search,), matches)
    return Candidates(Inferred[frame for frame in frames if !isnothing(frame)], !any(isnothing, frames))
end

"""The frame of method match `match`, inferred once per search's `frames`; `nothing` when inference cannot type it."""
function candidate_frame(search::CandidateSearch, match::Core.MethodMatch)::Union{Nothing, Inferred} # lint: unmarked-mutation  memoizes frames in the search
    instance = COMPILER.specialize_method(match)
    if !haskey(search.frames, instance)
        search.frames[instance] = typed_frame(COMPILER.NativeInterpreter(), match)
    end
    return search.frames[instance]
end

"""The name a site's detail gives candidate `method`: its module, name, file and line."""
candidate_name(method::Method)::String = "$(method.module).$(method.name) at $(basename(string(method.file))):$(method.line)"

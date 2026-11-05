# The frames an entry point compiles, found by walking optimized IR along `:invoke` edges and the
# callees inlined into it. The rules read the package's frames (`runtime_dispatches`).

"""
    mentions_module(signature, package, depth)

Whether `signature` names a type of `package` (`belongs`) anywhere in its parameters.
"""
function mentions_module(signature::Any, package::Package, depth::Integer)::Bool
    if depth > 6
        return false
    elseif signature isa UnionAll
        return mentions_module(signature.body, package, depth + 1)
    elseif signature isa Union
        return mentions_module(signature.a, package, depth + 1) ||
            mentions_module(signature.b, package, depth + 1)
    elseif !(signature isa DataType)
        return false
    end
    return belongs(parentmodule(signature), package) ||
        any(mentions_module.(collect(signature.parameters), (package,), depth + 1))
end

"""
    invoked_instance(callee)

The method instance an `:invoke` statement names: a `CodeInstance` on Julia 1.12 and later.
"""
invoked_instance(callee::Core.MethodInstance)::Core.MethodInstance = callee
invoked_instance(callee::Core.CodeInstance)::Union{Nothing, Core.MethodInstance} = invoked_instance(callee.def)
invoked_instance(::Any)::Nothing = nothing

"""
    frame_callees(ir, package)

The method instances `ir`, an optimized method body, calls that a walk of `package` follows: the
`:invoke` edges defined in `package` or with a signature naming one of its types (JET's
`target_modules` scope), and the inlined callees defined in `package`. Another module's inlined
callee needs no frame: its own calls are already in `ir`. No instance of a method that `ir` calls
past inference's recursion limit (`cut_off_instances`) is followed, so the walk ends.
"""
function frame_callees(ir::COMPILER.IRCode, package::Package)::Vector{Core.MethodInstance}
    expressions = [statement for statement in ir.stmts.stmt if statement isa Expr]
    invoked = [invoked_instance(first(statement.args)) for statement in expressions if statement.head in (:invoke, :invoke_modify)]
    inlined = collect(Core.MethodInstance, Iterators.flatten(inlined_instances.(ir.debuginfo.edges)))
    callees = Core.MethodInstance[filter(Base.Fix2(followed, package), invoked); filter(Base.Fix2(defined_in, package), inlined)]
    limited = cut_off_methods(ir)
    kept = Core.MethodInstance[] # lint: non-public-access  the walk's edges are method instances
    for callee in callees
        if !(callee.def in limited)
            push!(kept, callee)
        end
    end
    return kept
end

"""
Whether optimized statement `statement` invokes a method instance inference cut off at its recursion
limit: an `:invoke` whose callee has a concrete signature but no `CodeInstance`, since inference kept
no code for it.
"""
function cut_off(statement::Expr)::Bool # lint: abstract-local  IR operands are untyped
    callee = statement.head === :invoke ? first(statement.args) : nothing
    return callee isa Core.MethodInstance && Base.isdispatchtuple(callee.specTypes) # lint: non-public-access  an `:invoke` operand is a method instance
end
cut_off(::Any)::Bool = false

"""
The method instances `ir`, an optimized method body, invokes that inference cut off (`cut_off`).
Each nests its argument types deeper than its caller's, so a walk that followed one, or any other
instance of its method, would infer a new instance at every step and never finish.
"""
function cut_off_instances(ir::COMPILER.IRCode)::Vector{Core.MethodInstance} # lint: runtime-dispatch # lint: abstract-local # lint: non-public-access  IR statements are untyped; the cut-off operands are method instances
    found = Core.MethodInstance[] # lint: non-public-access  the cut-off operands are method instances
    for statement in ir.stmts.stmt
        if cut_off(statement)
            push!(found, first(statement.args))
        end
    end
    return found
end

"""The methods of the `cut_off_instances` of `ir`."""
cut_off_methods(ir::COMPILER.IRCode)::Vector{Method} = Method[instance.def for instance in cut_off_instances(ir)] # lint: non-public-access  the walk reads optimized IR

"""Whether `callee`, a method instance, is of a method `package` defines."""
defined_in(callee::Core.MethodInstance, package::Package)::Bool = callee.def isa Method && belongs(callee.def.module, package)

"""The method instances inlined at debug info `debuginfo`: its own `def`, and those inlined below it."""
inlined_instances(debuginfo::Core.DebugInfo)::Vector{Core.MethodInstance} = Core.MethodInstance[
    own_instance(debuginfo.def); collect(Core.MethodInstance, Iterators.flatten([inlined_instances(edge) for edge in debuginfo.edges]))
]

"""The method instance a debug info `def` names, as a vector of one; none for a method or a symbol."""
own_instance(def::Core.MethodInstance)::Vector{Core.MethodInstance} = [def]
own_instance(::Any)::Vector{Core.MethodInstance} = Core.MethodInstance[]

"""Whether a walk of `package` follows `callee`, an `invoked_instance`: a method of `package`, or one whose signature names a type of it."""
followed(callee::Any, package::Package)::Bool = callee isa Core.MethodInstance && callee.def isa Method &&
    (defined_in(callee, package) || mentions_module(callee.specTypes, package, 0))

"""
    entry_frames(seeds, target)

The `Inferred` frame of every method instance of `target`'s package (`belongs`) reachable from `seeds`
(entry-point call signatures such as `Tuple{typeof(f), Int}`) along `frame_callees` edges, the seeds
included. Each instance is inferred once; frames of other modules are walked through and dropped.
Under `--code-coverage` it warns once (`warn_coverage!`), since the frames then differ from the code users run.
"""
function entry_frames(seeds::AbstractVector{<:Type}, target::Module)::Vector{Inferred}
    warn_coverage!(Base.JLOptions().code_coverage) # lint: non-public-access  Base has no public accessor for the --code-coverage level
    return walk_frames(
        Package(target),
        unique(collect(Core.MethodInstance, Iterators.flatten(selected_instances.(seeds)))),
        Set{Core.MethodInstance}(),
        Inferred[],
    )
end

"""
Warn, once per logger, that the typed rules read code compiled under coverage when `coverage`
(`Base.JLOptions().code_coverage`) is not zero: coverage blocks inlining and constant folding, so the
frames differ from the code users run.
"""
function warn_coverage!(coverage::Integer)::Nothing
    if coverage != 0
        @warn "the typed rules read code compiled with --code-coverage, which blocks inlining and constant folding, so their findings can differ from the code users run; run them in `corset check`, outside Pkg.test" maxlog = 1
    end
    return nothing
end

"""
The `kept` frames, then the frames of `package` that the walk from `frontier` reaches, skipping the
method instances in `seen`.
"""
function walk_frames(
        package::Package,
        frontier::AbstractVector{Core.MethodInstance},
        seen::AbstractSet{Core.MethodInstance},
        kept::AbstractVector{Inferred},
    )::Vector{Inferred}
    if isempty(frontier)
        return kept
    end
    frames = Inferred[frame for frame in typed_frame.(frontier) if !isnothing(frame)]
    reached = union(seen, frontier)
    callees = unique(collect(Core.MethodInstance, Iterators.flatten(frame_callees.(getfield.(frames, :ir), (package,)))))
    owned = frames[belongs.(getfield.(getfield.(frames, :method), :module), (package,))]
    return walk_frames(package, filter(!in(reached), callees), reached, vcat(kept, owned))
end

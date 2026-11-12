# The fixers of `annotation` and `concrete-return`. They read the types inference found for each
# method in the frames of the loaded package, and write the most general annotation those types
# allow: an abstract supertype, `typeof(argument)`, or a type no narrower than what was observed.

"""Whether `type` is defined by Base or Core, so a name in it needs no qualification by the package."""
base_type(type::Type)::Bool = parentmodule(type) in (Base, Core) || Base.moduleroot(parentmodule(type)) in (Base, Core)

"""Whether the dotted `path` names `target` when looked up from `scope`."""
function binds(scope::Module, path::AbstractVector{Symbol}, target::Any)::Bool
    current = scope
    for part in path[1:(end - 1)]
        if !(isdefined(current, part) && getglobal(current, part) isa Module)
            return false
        end
        current = getglobal(current, part)::Module
    end
    return isdefined(current, last(path)) && getglobal(current, last(path)) === target
end

"""The names of `mod` and its parents, outermost first."""
function module_path(mod::Module)::Vector{Symbol}
    path = Symbol[nameof(mod)]
    parent = parentmodule(mod)
    while parent !== mod
        pushfirst!(path, nameof(parent))
        mod = parent
        parent = parentmodule(mod)
    end
    return path
end

"""The text naming `type`'s type constructor in `scope`: its bare name when `scope` resolves it, else its module path; `""` when neither resolves."""
function resolved_name(type::DataType, scope::Module)::String
    name = type.name.name
    for path in (Symbol[name], push!(module_path(type.name.module), name))
        if binds(scope, path, type.name.wrapper)
            return join(path, ".")
        end
    end
    return ""
end

"""The first abstract supertype of `type` besides `Any`, or `Any`."""
function abstract_supertype(type::DataType)::DataType
    parent = supertype(type)
    while parent !== Any && !isabstracttype(parent)
        parent = supertype(parent)
    end
    return parent
end

"""The types `type` is a `Union` of, or `type` alone."""
union_members(type::Type)::Vector{Type} = type isa Union ? vcat(union_members(type.a::Type), union_members(type.b::Type)) : Type[type]

"""The types whose text is their own name: every kin of one is named by it."""
const NAMED_FAMILIES = (Number, AbstractString, Symbol, AbstractChar, AbstractDict, AbstractSet, NamedTuple, Tuple, Function, Type)

"""The text of the supertype that holds `type` and its kin among numbers and the `NAMED_FAMILIES`, or `""`. An argument (`generous`) takes every real."""
function family_text(type::DataType, generous::Bool)::String
    if type <: Bool
        return "Bool"
    elseif type <: Real
        return generous ? "Real" : type <: Integer ? "Integer" : "Real"
    end
    for family in NAMED_FAMILIES
        if type <: family
            return string(nameof(family))
        end
    end
    return ""
end

"""
    wide_text(type, scope, generous)

Source text naming a type that holds `type` and its kin, or `""` when none is safe. `generous` is for
arguments, which should accept every number and array like the observed one (`Real`,
`AbstractVector{<:Real}`); a result keeps `Integer` and otherwise widens to `Real`; `AbstractFloat` blocks automatic differentiation.
"""
function wide_text(type::Type, scope::Module, generous::Bool)::String
    if type === Nothing || type === Missing
        return string(type)
    elseif type isa Union
        return union_text(type, scope, generous)
    elseif !(type isa DataType) || type === Any
        return ""
    end
    text = family_text(type, generous)
    if !isempty(text)
        return text
    end
    return type <: AbstractArray ? array_text(type, scope, generous) : struct_text(type, scope, generous)
end

"""The `Union{…}` text of the members of `type`, or `""` when any member has no safe text."""
function union_text(type::Union, scope::Module, generous::Bool)::String
    pieces = String[]
    for member in union_members(type)
        piece = wide_text(member, scope, generous)
        if isempty(piece)
            return ""
        end
        push!(pieces, piece)
    end
    return "Union{" * join(unique(pieces), ", ") * "}"
end

"""The `AbstractArray{T, N}` that array `type` is a subtype of."""
function array_supertype(type::DataType)::DataType
    parent = type
    while parent.name !== Base.typename(AbstractArray)
        parent === Any && throw(ArgumentError("$type is no AbstractArray"))
        parent = supertype(parent)
    end
    return parent
end

"""The `AbstractVector`, `AbstractMatrix` or `AbstractArray` text for array `type`, its element type generalized as `wide_text` does."""
function array_text(type::DataType, scope::Module, generous::Bool)::String
    parent = array_supertype(type)
    dimensions = parent.parameters[2]::Int
    name = dimensions == 1 ? "AbstractVector" : dimensions == 2 ? "AbstractMatrix" : "AbstractArray"
    if parent.parameters[1] === Any
        return name
    end
    inner = wide_text(parent.parameters[1]::Type, scope, generous)
    return isempty(inner) ? "" : dimensions <= 2 ? "$name{<:$inner}" : "$name{<:$inner, $dimensions}"
end

"""The text for struct `type`: its bare name as an argument, else its nearest abstract supertype (`""` for `Any`)."""
function struct_text(type::DataType, scope::Module, generous::Bool)::String
    if generous && !base_type(type)
        return resolved_name(type, scope)
    end
    parent = abstract_supertype(type)
    return parent === Any ? "" : resolved_name(parent, scope)
end

"""Whether the type `text` names, evaluated in `scope`, holds every one of `types`."""
holds_all(types::AbstractVector{<:Type}, text::String, scope::Module)::Bool = all(Base.Fix2(<:, Base.include_string(scope, text)::Type), types)

"""
The annotation text naming every one of `types`, or `""`. The text is evaluated in `scope` and kept
only when it holds every type.
"""
function annotation_text(types::AbstractVector{<:Type}, scope::Module, generous::Bool)::String
    pieces = String[]
    for type in types
        piece = wide_text(type, scope, generous)
        if isempty(piece) || (!generous && type isa Union)
            return ""
        end
        push!(pieces, piece)
    end
    pieces = unique(pieces)
    if isempty(pieces) || (!generous && length(pieces) > 1) || length(pieces) > 3
        return ""
    end
    text = length(pieces) == 1 ? only(pieces) : "Union{" * join(pieces, ", ") * "}"
    return holds_all(types, text, scope) ? text : ""
end

"""One method definition in a source file with the inferred frames of the method it defines: `observed` holds the entry walk's, `declared` the frames of the declared signature, and `frames` both."""
struct TypedDefinition
    node::SYNTAX.SyntaxNode
    call::SYNTAX.SyntaxNode
    spine::Vector{SYNTAX.SyntaxNode}
    frames::Vector{Inferred}
    observed::Vector{Inferred}
    declared::Vector{Inferred}
end

"""The signature nodes of `signature` from the outside in, down to its call: `where` and `::` wrappers, then the call."""
function signature_spine(signature::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    spine = SYNTAX.SyntaxNode[signature]
    while SYNTAX.kind(last(spine)) in (SYNTAX.@K_str("where"), SYNTAX.@K_str("::"))
        push!(spine, first(node_children(last(spine))))
    end
    return spine
end

"""The plain type of each inference lattice element of `elements`: the element when a type, the type of a constant's value, else `Any`."""
function lattice_types(elements::AbstractVector{<:Any})::Vector{Type}
    types = Type[]
    for index in eachindex(elements)
        push!(types, elements[index] isa Type ? elements[index]::Type : hasfield(typeof(elements[index]), :val) ? typeof(getfield(elements[index], :val)) : Any)
    end
    return types
end

"""The argument types of the method instance of `frame`, one per argument after the function itself."""
argument_types(frame::Inferred)::Vector{Type} = lattice_types((frame.code.slottypes::Vector{Any})[2:min(end, frame.method.nargs)])

"""The result type inference found for each of `frames`."""
result_types(frames::AbstractVector{Inferred})::Vector{Type} = lattice_types(Any[frame.code.rettype for frame in frames])

"""Whether `reference` is the global `name` of `mod`."""
is_global(reference::Any, mod::Module, name::Symbol)::Bool = reference isa GlobalRef && reference.mod === mod && reference.name === name

"""The statement number `operand` names when it is a reference to a statement's value, else 0."""
statement_number(operand::Any)::Int = nameof(typeof(operand)) === :SSAValue ? getfield(operand, :id)::Int : 0

"""Whether `call` is a call of `name` of `mod` with an operand."""
calls_global(call::Expr, mod::Module, name::Symbol)::Bool = call.head === :call && length(call.args) >= 2 && is_global(call.args[1], mod, name)

"""The call that lowered statement `index` of `code` makes or that statement assigns, as an expression; a statement that is no call gives an empty block."""
function call_at(code::AbstractVector{Any}, index::Int)::Expr # lint: unstable-variable  lowered code holds statements of any type
    statement = code[index]
    if !(statement isa Expr)
        return Expr(:block)
    end
    return statement.head === :(=) && last(statement.args) isa Expr ? last(statement.args)::Expr : statement
end

"""Whether statement `index` of `frame` calls `name` of `mod` with an operand and inference found it reachable."""
live_call(frame::Inferred, index::Int, mod::Module, name::Symbol)::Bool =
    calls_global(call_at(frame.code.code, index), mod, name) && (frame.code.ssavaluetypes::Vector{Any})[index] !== Union{}

"""The statement number of the first operand of the call that statement `index` of `frame` makes; 0 when it makes none."""
first_operand(frame::Inferred, index::Int)::Int = calls_global(call_at(frame.code.code, index), Core, :typeassert) ? statement_number(call_at(frame.code.code, index).args[2]) : 0

"""Whether `frame` converts its result to a declared return type: a live `convert` feeding a `typeassert`, so dropping the declaration changes the value."""
function converts_result(frame::Inferred)::Bool
    for index in eachindex(frame.code.code)
        source = first_operand(frame, index)
        if source > 0 && live_call(frame, index, Core, :typeassert) && live_call(frame, source, Base, :convert)
            return true
        end
    end
    return false
end

"""Macros that leave the function they wrap as written; any other macro (`@model`, `@generated`) may rewrite its signature and result."""
const TRANSPARENT_MACROS = ("views", "inline", "noinline", "inbounds", "propagate_inbounds", "nospecialize", "assume_effects", "doc")

"""Whether `node` sits inside a macro call that may rewrite it."""
function opaque_macro(node::SYNTAX.SyntaxNode)::Bool
    parent = node.parent
    while !isnothing(parent)
        if SYNTAX.kind(parent) === SYNTAX.@K_str("macrocall") && !(lstrip(SYNTAX.sourcetext(first(node_children(parent))), '@') in TRANSPARENT_MACROS)
            return true
        end
        parent = parent.parent
    end
    return false
end

"""The definitions of `source` whose signature has the plain shape the typed fixers rewrite, each with the frames of its method."""
function typed_definitions(source::Source, by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, observed_by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, declared_by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}})::Vector{TypedDefinition}
    found = TypedDefinition[]
    for node in definition_nodes(source.tree)
        spine = signature_spine(first(node_children(node)))
        call = last(spine)
        place = (source.path, first(SYNTAX.source_location(node)))
        if SYNTAX.kind(call) === CALL_KIND && !opaque_macro(node) && haskey(by_place, place) && !any(keyword_part, node_children(call)[2:end]) &&
                SYNTAX.kind(first(node_children(call))) in (IDENTIFIER_KIND, FIELD_KIND)
            frames = filter(Base.Fix2(declares_frame, call), by_place[place])
            if !isempty(frames)
                push!(found, TypedDefinition(node, call, spine, frames, filter(Base.Fix2(declares_frame, call), get(observed_by_place, place, Inferred[])), filter(Base.Fix2(declares_frame, call), get(declared_by_place, place, Inferred[]))))
            end
        end
    end
    return found
end

"""The frames of `frames` at each (file, line); one line can hold several definitions, which `declares_frame` tells apart."""
function frames_by_place(frames::AbstractVector{Inferred})::Dict{Tuple{String, Int}, Vector{Inferred}}
    places = Dict{Tuple{String, Int}, Vector{Inferred}}()
    for frame in frames
        if !frame.method.isva
            push!(get!(places, (string(frame.method.file), Int(frame.method.line)), Inferred[]), frame)
        end
    end
    return places
end

"""Whether `frame` is of the method that the signature call `call` defines: same name, and the method with every default filled in."""
function declares_frame(frame::Inferred, call::SYNTAX.SyntaxNode)::Bool
    written = SYNTAX.sourcetext(first(node_children(call)))
    return string(frame.method.name) == last(split(written, '.')) && frame.method.nargs == length(node_children(call))
end

"""
The frames inference gives the declared signature of each method of `mod`: their result covers every
argument the signature admits, not only the ones the entry walk saw. A safe result annotation needs one.
"""
function declared_frames(mod::Module)::Vector{Inferred}
    owned = Set{Method}(Base.invokelatest(defined_methods, mod)::Vector{Method})
    result = Inferred[]
    for method in owned
        if !method.isva
            append!(result, filter(Base.Fix2(owned_frame, owned), typed_frames(method.sig)))
        end
    end
    return result
end

"""Whether the method of `frame` is one of `owned`."""
owned_frame(frame::Inferred, owned::AbstractSet{Method})::Bool = frame.method in owned

"""The insertion of `text` at byte `position` of file `path`."""
insertion(path::String, position::Integer, text::String)::ByteRewrite = ByteRewrite(path, position:(position - 1), text)

"""The `edits` that annotate part of a definition, and whether they are `complete`: every part has a safe annotation, else the edits are none."""
struct Edits
    edits::Vector{ByteRewrite}
    complete::Bool
end

"""The edits that annotate the untyped arguments of `definition` from its frames' types; an untyped argument is incomplete unless `unsafe`, since a type observed in a few calls narrows dispatch."""
function argument_edits(source::Source, definition::TypedDefinition, scope::Module, unsafe::Bool)::Edits
    edits = ByteRewrite[]
    observed = Vector{Type}[argument_types(frame) for frame in definition.observed]
    for (index, argument) in enumerate(node_children(definition.call)[2:end])
        target = SYNTAX.kind(argument) === KEYWORD_KIND ? first(node_children(argument)) : argument
        if SYNTAX.kind(argument) === SYNTAX.@K_str("::")
            continue
        elseif !unsafe || SYNTAX.kind(target) !== IDENTIFIER_KIND || any(Base.Fix2(shorter_than, index), observed)
            return Edits(ByteRewrite[], false)
        end
        text = annotation_text(Type[types[index] for types in observed], scope, true)
        if isempty(text)
            return Edits(ByteRewrite[], false)
        end
        push!(edits, insertion(source.path, last(SYNTAX.byte_range(target)) + 1, "::" * text))
    end
    return Edits(edits, true)
end

"""Whether `types` has fewer than `count` entries."""
shorter_than(types::AbstractVector{<:Type}, count::Integer)::Bool = length(types) < count

"""Whether every frame of `frames` returns, at argument `index`, the type that argument has in that frame."""
function returns_argument(frames::AbstractVector{Inferred}, results::AbstractVector{<:Type}, index::Integer)::Bool
    for (frame, result) in zip(frames, results)
        types = argument_types(frame)
        if length(types) < index || types[index] != result
            return false
        end
    end
    return true
end

"""The text of the result annotation for `definition`, `""` in safe mode without a declared-signature frame: `typeof(argument)` when every frame returns its argument's type, else a general type; `""` for none."""
function result_text(definition::TypedDefinition, scope::Module, unsafe::Bool)::String
    if !unsafe && isempty(definition.declared)
        return ""
    end
    results = result_types(definition.frames)
    constructed = constructor_text(definition, results)
    if !isempty(constructed)
        return constructed
    end
    for (index, written) in enumerate(node_children(definition.call)[2:end])
        argument = SYNTAX.kind(written) in (SYNTAX.@K_str("::"), KEYWORD_KIND) ? first(node_children(written)) : written
        if SYNTAX.kind(argument) === IDENTIFIER_KIND && returns_argument(definition.frames, results, index) && (unsafe || !(first(results) isa Union))
            return "typeof($(SYNTAX.sourcetext(argument)))"
        end
    end
    return Union{} in results ? "" : annotation_text(results, scope, unsafe)
end

"""The result annotation of a constructor: the bare name of the type its call names, when every frame returns that type; else `""`."""
function constructor_text(definition::TypedDefinition, results::AbstractVector{<:Type})::String
    name = SYNTAX.sourcetext(first(node_children(definition.call)))
    return !isempty(results) && all(type -> type isa DataType && string(nameof(type)) == name, results) ? name : ""
end

"""Whether definition `node` is in short form (`f(x) = …`)."""
short_form(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.has_flags(node, SYNTAX.SHORT_FORM_FUNCTION_FLAG)

"""The edits that add result annotation `text` to `definition`, parenthesized when a short-form `where` would otherwise bind it."""
function result_edits(source::Source, definition::TypedDefinition, text::String)::Vector{ByteRewrite}
    call_range = SYNTAX.byte_range(definition.call)
    if short_form(definition.node) && length(definition.spine) > 1
        return [insertion(source.path, first(call_range), "("), insertion(source.path, last(call_range) + 1, "::$text)")]
    end
    return [insertion(source.path, last(call_range) + 1, "::$text")]
end

"""The site of `definition`, from its first line to the end of its signature, so a `# lint:` opt-out there keeps it."""
function typed_site(source::Source, definition::TypedDefinition)::Site
    signature = first(node_children(definition.node))
    return Site(source.name, source.path, first(SYNTAX.source_location(definition.node)), first(SYNTAX.source_location(definition.node.source, last(SYNTAX.byte_range(signature)))), "")
end

"""Whether the spine of `definition` declares a result type."""
declares_result(definition::TypedDefinition)::Bool = any(node -> SYNTAX.kind(node) === SYNTAX.@K_str("::"), definition.spine)

"""The scope in which the types of `definition` are named: the module of its method."""
definition_scope(definition::TypedDefinition)::Module = first(definition.frames).method.module

"""The repairs for the `annotation` rule in `source`: a definition with an unannotated argument or result is fixed whole or not at all, or in part when `unsafe`."""
function annotation_repairs(source::Source, by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, observed_by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, declared_by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, unsafe::Bool)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for definition in typed_definitions(source, by_place, observed_by_place, declared_by_place)
        scope = definition_scope(definition)
        arguments = argument_edits(source, definition, scope, unsafe)
        results = declares_result(definition) ? Edits(ByteRewrite[], true) : result_edits_for(source, definition, scope, unsafe)
        edits = vcat(arguments.edits, results.edits)
        if (unsafe || (arguments.complete && results.complete)) && !isempty(edits)
            append!(repairs, Repair.((typed_site(source, definition),), edits))
        end
    end
    return repairs
end

"""The edits that annotate the result of `definition`, incomplete when no safe annotation exists."""
function result_edits_for(source::Source, definition::TypedDefinition, scope::Module, unsafe::Bool)::Edits
    text = result_text(definition, scope, unsafe)
    return isempty(text) ? Edits(ByteRewrite[], false) : Edits(result_edits(source, definition, text), true)
end

"""
    typed_plan(repairs_in, repository, directories, mod, frames, unsafe)

The `FixPlan` of the repairs `repairs_in` finds in each source of `directories`, given the frames of `mod`: the entry walk's
`frames` and the frames of each declared signature. `unsafe` lets them change behavior.
"""
function typed_plan(repairs_in::Function, repository::Repository, directories::Tuple{Vararg{String}}, mod::Module, frames::AbstractVector{Inferred}, unsafe::Bool)::FixPlan{ByteRewrite, typeof(rewritten_texts)}
    declared = declared_frames(mod)
    by_place = frames_by_place(vcat(frames, declared))
    repairs = Repair{ByteRewrite}[]
    for source in directory_sources(repository, directories)
        append!(repairs, repairs_in(source, by_place, frames_by_place(frames), frames_by_place(declared), unsafe))
    end
    return FixPlan(repairs, rewritten_texts)
end

"""
    annotation_plan(repository, directories, mod, frames, unsafe)

The `FixPlan` that annotates the arguments and results of methods from the types inference found. `unsafe` also
annotates arguments, joins disagreeing specializations and writes `Union` results.
"""
annotation_plan(repository::Repository, directories::Tuple{Vararg{String}}, mod::Module, frames::AbstractVector{Inferred}, unsafe::Bool)::FixPlan{ByteRewrite, typeof(rewritten_texts)} =
    typed_plan(annotation_repairs, repository, directories, mod, frames, unsafe)

"""The repairs for the `concrete-return` rule in `source`: a declared concrete result is replaced when no frame converts to it and inference found a general type."""
function concrete_return_repairs(source::Source, by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, ::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, declared_by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, unsafe::Bool)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for definition in typed_definitions(source, by_place, by_place, declared_by_place)
        declared = filter(node -> SYNTAX.kind(node) === SYNTAX.@K_str("::"), definition.spine)
        scope = definition_scope(definition)
        expression = Expr(definition.node)::Expr
        if isempty(declared) || !names_concrete_type(return_annotation(expression), scope, where_variables(expression)) ||
                constructs_own_type(expression) || (!unsafe && any(converts_result, definition.frames))
            continue
        end
        text = result_text(definition, scope, unsafe)
        if !isempty(text)
            edit = ByteRewrite(source.path, SYNTAX.byte_range(last(node_children(first(declared)))), text)
            push!(repairs, Repair(typed_site(source, definition), edit))
        end
    end
    return repairs
end

"""
    concrete_return_plan(repository, directories, mod, frames, unsafe)

The `FixPlan` that replaces a declared concrete result type with a general one, where inference shows the body already returns it.
"""
concrete_return_plan(repository::Repository, directories::Tuple{Vararg{String}}, mod::Module, frames::AbstractVector{Inferred}, unsafe::Bool)::FixPlan{ByteRewrite, typeof(rewritten_texts)} =
    typed_plan(concrete_return_repairs, repository, directories, mod, frames, unsafe)

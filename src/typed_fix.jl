# The fixers of `annotation` and `concrete-return`. They read the types inference found for each
# method in the frames of the loaded package, and write the most general annotation those types
# allow: an abstract supertype, `typeof(argument)`, or a type no narrower than what was observed.

"""Whether `type` is defined by Base or Core, so a name in it needs no qualification by the package."""
base_type(type::Type)::Bool = parentmodule(type) in (Base, Core) || Base.moduleroot(parentmodule(type)) in (Base, Core)

"""The text naming `wrapper` in `scope`: its bare name when `scope` resolves it, else its module path; `""` when neither resolves."""
function resolved_name(wrapper::Any, scope::Module)::String
    name = string(nameof(wrapper))
    for candidate in (name, join(fullname(parentmodule(wrapper)), ".") * "." * name)
        try
            if Core.eval(scope, Meta.parse(candidate)) === wrapper
                return candidate
            end
        catch
            continue
        end
    end
    return ""
end

"""The first abstract supertype of `type` besides `Any`, or `Any`."""
function abstract_supertype(type::Type)::Type
    parent = supertype(type)
    while parent !== Any && !isabstracttype(parent)
        parent = supertype(parent)
    end
    return parent
end

"""
    wide_text(type, scope, generous)

Source text naming a type that holds `type` and its kin, or `""` when none is safe. `generous` is for
arguments, which should accept every number and array like the observed one (`Real`,
`AbstractVector{<:Real}`); a result keeps its class (`Integer`, `AbstractFloat`).
"""
function wide_text(type::Any, scope::Module, generous::Bool)::String
    if type === Nothing || type === Missing
        return string(type)
    elseif type isa Union
        pieces = wide_text.(Base.uniontypes(type), (scope,), (generous,))
        return any(isempty, pieces) ? "" : "Union{" * join(unique(pieces), ", ") * "}"
    elseif !(type isa DataType) || type === Any
        return ""
    elseif type === Bool
        return "Bool"
    elseif type <: Integer || type <: AbstractFloat
        return generous ? "Real" : (type <: Integer ? "Integer" : "AbstractFloat")
    elseif type <: Real || type <: Number
        return type <: Real ? "Real" : "Number"
    elseif type <: AbstractString
        return "AbstractString"
    elseif type === Symbol || type <: AbstractChar
        return type === Symbol ? "Symbol" : "AbstractChar"
    elseif type <: AbstractArray
        return array_text(type, scope, generous)
    elseif type <: AbstractDict || type <: AbstractSet
        return type <: AbstractDict ? "AbstractDict" : "AbstractSet"
    elseif type <: NamedTuple
        return "NamedTuple"
    elseif type <: Tuple
        return "Tuple"
    elseif type <: Function
        return "Function"
    elseif type <: Type
        return "Type"
    end
    return struct_text(type, scope, generous)
end

"""The `AbstractVector`, `AbstractMatrix` or `AbstractArray` text for array `type`, its element type generalized as `wide_text` does."""
function array_text(type::DataType, scope::Module, generous::Bool)::String
    name = ndims(type) == 1 ? "AbstractVector" : ndims(type) == 2 ? "AbstractMatrix" : "AbstractArray"
    element = eltype(type)
    inner = wide_text(element, scope, generous)
    if element === Any
        return name
    elseif isempty(inner)
        return ""
    end
    return ndims(type) <= 2 ? "$name{<:$inner}" : "$name{<:$inner, $(ndims(type))}"
end

"""The text for struct `type`: its bare name as an argument, else its nearest abstract supertype (`""` for `Any`)."""
function struct_text(type::DataType, scope::Module, generous::Bool)::String
    if !base_type(type) && generous
        return resolved_name(type.name.wrapper, scope)
    end
    parent = abstract_supertype(type)
    return parent === Any ? "" : resolved_name(Base.unwrap_unionall(parent).name.wrapper, scope)
end

"""
The annotation text naming every one of `types`, or `""`. The text is evaluated in `scope` and kept
only when it holds every type.
"""
function annotation_text(types::AbstractVector{<:Any}, scope::Module, generous::Bool)::String
    if !generous && any(type -> type isa Union, types)
        return ""
    end
    pieces = unique(wide_text.(types, (scope,), (generous,)))
    if isempty(pieces) || any(isempty, pieces) || (!generous && length(pieces) > 1) || length(pieces) > 3
        return ""
    end
    text = length(pieces) == 1 ? only(pieces) : "Union{" * join(pieces, ", ") * "}"
    try
        named = Core.eval(scope, Meta.parse(text))
        return all(type -> type <: named, types) ? text : ""
    catch
        return ""
    end
end

"""One method definition in a source file with the inferred frames of the method it defines."""
struct TypedDefinition
    node::SYNTAX.SyntaxNode
    call::SYNTAX.SyntaxNode
    spine::Vector{SYNTAX.SyntaxNode}
    frames::Vector{Inferred}
end

"""The signature nodes of `signature` from the outside in, down to its call: `where` and `::` wrappers, then the call."""
function signature_spine(signature::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    spine = SYNTAX.SyntaxNode[signature]
    while SYNTAX.kind(last(spine)) in (SYNTAX.@K_str("where"), SYNTAX.@K_str("::"))
        push!(spine, first(node_children(last(spine))))
    end
    return spine
end

"""The argument types of the method instance of `frame`, one per argument after the function itself."""
function argument_types(frame::Inferred)::Vector{Any}
    parent = frame.code.parent
    types = parent isa Core.MethodInstance ? Base.unwrap_unionall(parent.specTypes).parameters : frame.code.slottypes
    return Any[COMPILER.widenconst(type isa TypeVar ? type.ub : type) for type in types[2:min(end, frame.method.nargs)]]
end

"""The result type inference found for `frame`."""
result_type(frame::Inferred)::Any = COMPILER.widenconst(frame.code.rettype)

"""Whether `frame` converts its result to a declared return type: a live `convert` feeding a `typeassert`, so dropping the declaration changes the value."""
function converts_result(frame::Inferred)::Bool
    code = frame.code.code
    types = frame.code.ssavaluetypes
    for (index, statement) in enumerate(code)
        call = statement isa Expr && statement.head === :(=) ? last(statement.args) : statement
        if call isa Expr && call.head === :call && length(call.args) >= 2 && is_global(first(call.args), Core, :typeassert) && types[index] !== Union{}
            source = call.args[2]
            inner = source isa Core.SSAValue ? code[source.id] : nothing
            if inner isa Expr && inner.head === :call && is_global(first(inner.args), Base, :convert) && types[source.id] !== Union{}
                return true
            end
        end
    end
    return false
end

"""Whether `reference` is the global `name` of `mod`."""
is_global(reference::Any, mod::Module, name::Symbol)::Bool = reference isa GlobalRef && reference.mod === mod && reference.name === name

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
function typed_definitions(source::Source, by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}})::Vector{TypedDefinition}
    found = TypedDefinition[]
    for node in definition_nodes(source.tree)
        parts = node_children(node)
        spine = signature_spine(first(parts))
        call = last(spine)
        place = (source.path, first(SYNTAX.source_location(node)))
        if SYNTAX.kind(call) === CALL_KIND && !opaque_macro(node) && haskey(by_place, place) && !any(keyword_part, node_children(call)[2:end]) &&
                SYNTAX.kind(first(node_children(call))) in (IDENTIFIER_KIND, FIELD_KIND)
            push!(found, TypedDefinition(node, call, spine, by_place[place]))
        end
    end
    return found
end

"""The frames of the longest method at each (file, line) of `frames`, which is the method a definition declares with its defaults filled in."""
function frames_by_place(frames::AbstractVector{Inferred})::Dict{Tuple{String, Int}, Vector{Inferred}}
    places = Dict{Tuple{String, Int}, Vector{Inferred}}()
    for frame in filter(frame -> !frame.method.isva, frames)
        push!(get!(places, (string(frame.method.file), Int(frame.method.line)), Inferred[]), frame)
    end
    for (place, found) in places
        longest = maximum(frame.method.nargs for frame in found)
        places[place] = filter(frame -> frame.method.nargs == longest, found)
    end
    return places
end

"""
The `frames` plus, for each method of `mod` none of them covers, the frames inference gives its declared
signature: a method the entry walk never reached still has a result type, and an argument annotated
already needs no observed type.
"""
function with_declared_frames(frames::AbstractVector{Inferred}, mod::Module)::Vector{Inferred}
    covered = Set{Method}(frame.method for frame in frames)
    declared = Inferred[]
    for method in defined_methods(mod)
        if !(method in covered) && !method.isva
            try
                append!(declared, typed_frames(method.sig))
            catch
                continue
            end
        end
    end
    return Inferred[frames; filter(frame -> frame.method in defined_methods(mod), declared)]
end

"""The insertion of `text` at byte `position` of file `path`."""
insertion(path::String, position::Integer, text::String)::ByteRewrite = ByteRewrite(path, position:(position - 1), text)

"""The edits that annotate the untyped arguments of `definition` from its frames' types, or `nothing` when any argument has no safe annotation."""
function argument_edits(source::Source, definition::TypedDefinition, scope::Module)::Union{Vector{ByteRewrite}, Nothing}
    edits = ByteRewrite[]
    observed = argument_types.(definition.frames)
    for (index, argument) in enumerate(node_children(definition.call)[2:end])
        target = SYNTAX.kind(argument) === KEYWORD_KIND ? first(node_children(argument)) : argument
        if SYNTAX.kind(argument) === SYNTAX.@K_str("::")
            continue
        elseif SYNTAX.kind(target) !== IDENTIFIER_KIND || any(frame -> length(frame) < index, observed)
            return nothing
        end
        text = annotation_text([frame[index] for frame in observed], scope, true)
        if isempty(text)
            return nothing
        end
        push!(edits, insertion(source.path, last(SYNTAX.byte_range(target)) + 1, "::" * text))
    end
    return edits
end

"""The text of the result annotation for `definition`: `typeof(argument)` when every frame returns its argument's type, else a general type; `""` for none."""
function result_text(definition::TypedDefinition, scope::Module, unsafe::Bool)::String
    results = result_type.(definition.frames)
    arguments = argument_types.(definition.frames)
    constructed = constructor_text(definition, results)
    if !isempty(constructed)
        return constructed
    end
    for (index, written) in enumerate(node_children(definition.call)[2:end])
        argument = SYNTAX.kind(written) in (SYNTAX.@K_str("::"), KEYWORD_KIND) ? first(node_children(written)) : written
        if SYNTAX.kind(argument) === IDENTIFIER_KIND && all(frame -> length(frame) >= index, arguments) &&
                all(position -> arguments[position][index] == results[position], eachindex(results)) && (unsafe || !(results[1] isa Union))
            return "typeof($(SYNTAX.sourcetext(argument)))"
        end
    end
    return any(==(Union{}), results) ? "" : annotation_text(results, scope, unsafe)
end

"""The result annotation of a constructor: the bare name of the type its call names, when every frame returns that type; else `""`."""
function constructor_text(definition::TypedDefinition, results::AbstractVector{<:Any})::String
    name = SYNTAX.sourcetext(first(node_children(definition.call)))
    named = all(type -> type isa DataType && string(nameof(type)) == name, results)
    return named && !isempty(results) ? name : ""
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

"""The repairs for the `annotation` rule in `source`: a definition with an unannotated argument or result is fixed whole or not at all."""
function annotation_repairs(source::Source, by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, unsafe::Bool)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for definition in typed_definitions(source, by_place)
        scope = first(definition.frames).method.module
        arguments = argument_edits(source, definition, scope)
        results = declares_result(definition) ? ByteRewrite[] : nothing
        if isnothing(results)
            guess = unsafe ? guess_result(definition) : Guess("", "", false)
            if guess.skipped
                continue
            end
            text = isempty(guess.text) ? result_text(definition, scope, unsafe) : guess.text
            results = isempty(text) ? nothing : result_edits(source, definition, text)
        end
        if unsafe
            arguments = something(arguments, ByteRewrite[])
            results = something(results, ByteRewrite[])
        end
        if isnothing(arguments) || isnothing(results) || isempty(vcat(arguments, results))
            continue
        end
        site = typed_site(source, definition)
        append!(repairs, Repair.((site,), vcat(arguments, results)))
    end
    return repairs
end

"""
    annotation_plan(repository, directories, mod, frames, unsafe)

The `FixPlan` that annotates the arguments and results of methods from the types inference found. `unsafe` also
annotates part of a definition, joins disagreeing specializations and writes `Union` results.
"""
function annotation_plan(repository::Repository, directories::Tuple{Vararg{String}}, mod::Module, frames::AbstractVector{Inferred}, unsafe::Bool)::FixPlan{ByteRewrite, typeof(rewritten_texts)}
    by_place = frames_by_place(with_declared_frames(frames, mod))
    repairs = [repair for source in directory_sources(repository, directories) for repair in annotation_repairs(source, by_place, unsafe)]
    return FixPlan(Repair{ByteRewrite}[repairs...], rewritten_texts)
end

"""The repairs for the `concrete-return` rule in `source`: a declared concrete result is replaced when no frame converts to it and inference found a general type."""
function concrete_return_repairs(source::Source, by_place::AbstractDict{Tuple{String, Int}, Vector{Inferred}}, unsafe::Bool)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for definition in typed_definitions(source, by_place)
        declared = filter(node -> SYNTAX.kind(node) === SYNTAX.@K_str("::"), definition.spine)
        scope = first(definition.frames).method.module
        expression = Expr(definition.node)
        if isempty(declared) || !names_concrete_type(return_annotation(expression), scope, where_variables(expression)) ||
                constructs_own_type(expression) || (!unsafe && any(converts_result, definition.frames))
            continue
        end
        guess = unsafe ? widen_guess(definition, scope) : Guess("", "", false)
        if guess.skipped
            continue
        end
        text = isempty(guess.text) ? result_text(definition, scope, unsafe) : guess.text
        if !isempty(text)
            annotation = last(node_children(first(declared)))
            edit = ByteRewrite(source.path, SYNTAX.byte_range(annotation), text)
            push!(repairs, Repair(typed_site(source, definition), edit))
        end
    end
    return repairs
end

"""
    concrete_return_plan(repository, directories, mod, frames, unsafe)

The `FixPlan` that replaces a declared concrete result type with a general one, where inference shows the body already returns it.
"""
function concrete_return_plan(repository::Repository, directories::Tuple{Vararg{String}}, mod::Module, frames::AbstractVector{Inferred}, unsafe::Bool)::FixPlan{ByteRewrite, typeof(rewritten_texts)}
    by_place = frames_by_place(with_declared_frames(frames, mod))
    repairs = [repair for source in directory_sources(repository, directories) for repair in concrete_return_repairs(source, by_place, unsafe)]
    return FixPlan(Repair{ByteRewrite}[repairs...], rewritten_texts)
end

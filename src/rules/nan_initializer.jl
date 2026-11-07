# The rule `nan-initializer` and its fixer: an array built by `zeros`, `ones` or `fill` and then written is
# initialized with NaN, so an element no write reached shows. The fixer proves that every element is written before
# any read (`x .= …`, or a loop over all indices whose first use of `x` is `x[i, …] = …`); other written arrays are only flagged.

# Element types that have no NaN, so an array of them gets no NaN initializer.
const NANLESS_TYPES = (
    "Int", "Int8", "Int16", "Int32", "Int64", "Int128", "UInt", "UInt8", "UInt16", "UInt32", "UInt64", "UInt128", "Bool", "Integer",
    "BigInt", "Cint", "Cuint", "Clong", "Culong", "Cchar", "Cuchar", "Cshort", "Cushort", "Clonglong", "Culonglong",
)

# The only element types the fixer rewrites; any other type text (a type parameter, `eltype(y)`, `Rational{Int}`) may have no NaN.
const FLOAT_TYPES = ("Float16", "Float32", "Float64", "BFloat16")

# The element text for a type the rule cannot classify.
const UNKNOWN_ELEMENT = "?"

# The element text of a `fill` whose value has no recognizable type; such a call is not reported.
const UNTYPED_FILL = "!"

# Kinds of syntax that end an iteration early or skip its writes.
const BROADCAST_ASSIGN_KIND = SYNTAX.@K_str(".=")
const EXIT_KINDS = (SYNTAX.@K_str("break"), SYNTAX.@K_str("continue"), SYNTAX.@K_str("return"))

# How an initializer array is judged: `:initializer` (every element written before any read, fixable), `:unproven`
# (written, but not provably an initializer) or `:nanless` (an integer or Bool array, which has no NaN).
"""One constant-array constructor `call` (`zeros`, `ones` or `fill`) of an array that is written, with its `proof`, the `element` type text (`""` for Float64) and its `dimensions` text."""
struct NanInitializer
    call::SYNTAX.SyntaxNode
    name::String
    proof::Symbol
    element::String
    dimensions::Vector{String}
    template::String
end

# Calls that build a local array, which then serves as a template. `copy` and `rand` are absent: they also return dictionaries, strings and scalars.
const ARRAY_BUILDERS = ("similar", "collect", "zeros", "ones", "fill", "Vector", "Matrix", "Array")

"""Whether the call syntax `call` builds an array: a call of `ARRAY_BUILDERS` (`fill` needs a dimension, or it is zero-dimensional)."""
function builds_array(call::SYNTAX.SyntaxNode)::Bool
    if SYNTAX.kind(call) !== CALL_KIND || !is_prefix_call(call)
        return false
    end
    head = first(node_children(call))
    name = callee_name(SYNTAX.kind(head) === SYNTAX.@K_str("curly") ? first(node_children(head)) : head)
    arguments = filter(!keyword_part, node_children(call)[2:end])
    return name in ARRAY_BUILDERS && !any(names_static_array, arguments) && (name != "fill" || length(arguments) >= 2)
end

"""Whether `statement` is `variable = <array-building call>`."""
function assigns_array(statement::SYNTAX.SyntaxNode, variable::String)::Bool
    parts = node_children(statement)
    return SYNTAX.kind(statement) === SYNTAX.@K_str("=") && length(parts) == 2 && is_identifier(first(parts), variable) && builds_array(last(parts))
end

"""The parameter syntax of the function definition syntax `definition`: those of its signature call, or of an anonymous `function (x, y)` tuple."""
function definition_parameters(definition::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    signature = first(node_children(definition))
    while SYNTAX.kind(signature) in (SYNTAX.@K_str("where"), SYNTAX.@K_str("::")) && !isempty(node_children(signature))
        signature = first(node_children(signature))
    end
    return SYNTAX.kind(signature) === CALL_KIND ? node_children(signature)[2:end] : node_children(signature)
end

"""
The number of places in syntax `node` and below that bind the name `variable`: assignments (destructuring included), `for` and
comprehension variables, lambda and `do` arguments, `catch` variables, `let`, `local` and `global` names and function parameters.
"""
function binding_count(node::SYNTAX.SyntaxNode, variable::String)::Int
    children = node_children(node)
    kind = SYNTAX.kind(node)
    own = 0
    if isempty(children)
        return own
    elseif kind in (SYNTAX.@K_str("="), SYNTAX.@K_str("op="), SYNTAX.@K_str("in"), SYNTAX.@K_str("->"), SYNTAX.@K_str("do"), SYNTAX.@K_str("catch"), SYNTAX.@K_str("local"), SYNTAX.@K_str("global"))
        own = binds_name(first(children), variable) ? 1 : 0
    elseif kind === SYNTAX.@K_str("macrocall")
        # A macro may bind a name it is given (`@variables x`), so a bare name argument counts.
        own = count(Base.Fix2(is_identifier, variable), children)
    elseif kind === SYNTAX.@K_str("let")
        own = count(Base.Fix2(is_identifier, variable), node_children(first(children)))
    elseif kind === SYNTAX.@K_str("function")
        own = count(Base.Fix2(binds_name, variable), definition_parameters(node))
    end
    return own + sum(Base.Fix2(binding_count, variable), children; init = 0)
end

# Syntax that opens a scope a binding does not leave: the scopes of `enclosing_scope` and the `do` closure.
const CLOSURE_KINDS = (SCOPE_KINDS..., SYNTAX.@K_str("do"))

"""The syntax nodes of `CLOSURE_KINDS` around `node`, innermost first."""
function closures_around(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    found = SYNTAX.SyntaxNode[]
    current = node.parent
    while !isnothing(current)
        if SYNTAX.kind(current) in CLOSURE_KINDS
            push!(found, current)
        end
        current = current.parent
    end
    return found
end

"""The outermost function, lambda or `let` syntax around `node`: the whole region in which a name can be rebound under it."""
function outermost_scope(node::SYNTAX.SyntaxNode)::SYNTAX.SyntaxNode
    outermost = node
    current = node.parent
    while !isnothing(current)
        outermost = SYNTAX.kind(current) in CLOSURE_KINDS ? current : outermost
        current = current.parent
    end
    return outermost
end

"""Whether syntax `node` or anything below it is `variable = <array-building call>` that ends before `call` and sits in a closure that also holds `call` or one around it."""
function assigns_array_before(node::SYNTAX.SyntaxNode, variable::String, call::SYNTAX.SyntaxNode)::Bool
    if assigns_array(node, variable) && last(SYNTAX.byte_range(node)) < first(SYNTAX.byte_range(call)) && visible_from(node, call)
        return true
    end
    for child in node_children(node)
        if assigns_array_before(child, variable, call)
            return true
        end
    end
    return false
end

"""Whether the binding `node` is in a closure that is `call`'s own closure or one around it."""
function visible_from(node::SYNTAX.SyntaxNode, call::SYNTAX.SyntaxNode)::Bool
    own = closures_around(node)
    return isempty(own) || any(Base.Fix1(===, first(own)), closures_around(call))
end

"""Whether `variable` is a local array at `call`: the whole outermost function binds the name exactly once, in an array-building assignment before `call`."""
function local_array(call::SYNTAX.SyntaxNode, variable::String)::Bool
    scope = outermost_scope(call)
    return binding_count(scope, variable) == 1 && assigns_array_before(scope, variable, call)
end

"""Whether `variable` is an array parameter annotated as one that the whole outermost function binds exactly once, as that parameter."""
array_parameter(call::SYNTAX.SyntaxNode, variable::String)::Bool = annotated_array(call, variable) && binding_count(outermost_scope(call), variable) == 1

"""The array variable `x` that a dimension text of `dimensions` names as `length(x)` or `size(x)` when `x` is an array argument or local at `call`, else `""`."""
function dimension_template(call::SYNTAX.SyntaxNode, dimensions::AbstractVector{<:AbstractString})::String
    for dimension in dimensions
        for found in eachmatch(r"^(?:length|size)\((\w+)\)$", dimension)
            candidate = string(only(found.captures))
            if array_parameter(call, candidate) || local_array(call, candidate)
                return candidate
            end
        end
    end
    return ""
end

"""Whether the `read` of an array is the target of an accumulation `x[i] += …`, `x .+= …` or `x += …`: it reads its start value."""
function is_accumulation(read::SYNTAX.SyntaxNode)::Bool
    node = read
    parent = node.parent
    if !isnothing(parent) && SYNTAX.kind(parent) === SYNTAX.@K_str("ref") && first(node_children(parent)) === node
        node = parent
        parent = node.parent
    end
    return !isnothing(parent) && SYNTAX.kind(parent) in (SYNTAX.@K_str("op="), SYNTAX.@K_str(".op=")) && first(node_children(parent)) === node
end

"""The element type text and dimension texts of the call syntax `call` of `zeros`, `ones` or `fill`, as `(type, dimensions)` with `type == ""` for Float64, or `UNTYPED_FILL` as the type when a `fill` value has an unknown type."""
function element_and_dimensions(call::SYNTAX.SyntaxNode, name::String)::Tuple{String, Vector{String}}
    arguments = filter(!keyword_part, node_children(call)[2:end])
    texts = String[SYNTAX.sourcetext(argument) for argument in arguments]
    if name == "fill"
        value = first(arguments)
        kind = SYNTAX.kind(value)
        if kind === SYNTAX.@K_str("Float32")
            return ("Float32", texts[2:end])
        elseif kind === SYNTAX.@K_str("Float")
            return ("", texts[2:end])
        elseif kind === SYNTAX.@K_str("Integer") || kind === SYNTAX.@K_str("Bool")
            return ("Int", texts[2:end])
        elseif kind === CALL_KIND && is_prefix_call(value) && constructor_name(first(node_children(value))) in ("zero", "one", "oneunit") && length(node_children(value)) == 2 && names_type(node_children(value)[2])
            return (known_element(SYNTAX.sourcetext(node_children(value)[2])), texts[2:end])
        end
        return (UNTYPED_FILL, String[])
    end
    # A bare variable before more dimensions may be the element type (`zeros(elty, n)`).
    typed = !isempty(arguments) && (names_type(first(arguments)) || (length(arguments) > 1 && SYNTAX.kind(first(arguments)) === IDENTIFIER_KIND))
    return typed ? (known_element(texts[1]), texts[2:end]) : ("", texts)
end

"""`text` when it names a float type or a NaN-less type, else `UNKNOWN_ELEMENT`: a type parameter or any other type text may have no NaN, and a capitalized first argument may be a dimension."""
known_element(text::AbstractString)::String = text in FLOAT_TYPES || text in NANLESS_TYPES ? String(text) : UNKNOWN_ELEMENT

"""The loop variables of the `for` syntax `loop` with the range syntax each runs over, as `(name, range)` pairs."""
function loop_ranges(loop::SYNTAX.SyntaxNode)::Vector{Tuple{String, SYNTAX.SyntaxNode}}
    ranges = Tuple{String, SYNTAX.SyntaxNode}[]
    for spec in node_children(first(node_children(loop)))
        if SYNTAX.kind(spec) === SYNTAX.@K_str("in") && SYNTAX.kind(first(node_children(spec))) === IDENTIFIER_KIND
            push!(ranges, (String(SYNTAX.sourcetext(first(node_children(spec)))), last(node_children(spec))))
        end
    end
    return ranges
end

"""Whether range syntax `range` runs over the whole of dimension `dimension` of the array `name` of `dimensions` dimensions."""
function covers_dimension(range::SYNTAX.SyntaxNode, name::String, dimension::Int, dimensions::Int)::Bool
    if SYNTAX.kind(range) === CALL_KIND && is_prefix_call(range)
        arguments = node_children(range)[2:end]
        called = call_name(range)
        if called == "eachindex"
            return dimensions == 1 && length(arguments) == 1 && is_identifier(only(arguments), name)
        elseif called == "axes"
            return length(arguments) == 2 && is_identifier(first(arguments), name) && SYNTAX.kind(last(arguments)) === SYNTAX.@K_str("Integer") && SYNTAX.sourcetext(last(arguments)) == string(dimension)
        end
    end
    return false
end

"""Whether the assignment `write` is `name[i, …] = …` with the loop variables of `ranges` as its indices, each ranging over the whole of its dimension."""
function writes_every_index(write::SYNTAX.SyntaxNode, name::String, ranges::AbstractVector{<:Tuple{String, SYNTAX.SyntaxNode}})::Bool
    target = first(node_children(write))
    if SYNTAX.kind(write) !== SYNTAX.@K_str("=") || SYNTAX.kind(target) !== SYNTAX.@K_str("ref") || !is_identifier(first(node_children(target)), name)
        return false
    end
    indices = node_children(target)[2:end]
    spans = Dict(variable => range for (variable, range) in ranges)
    for (dimension, index) in enumerate(indices)
        if SYNTAX.kind(index) !== IDENTIFIER_KIND || !haskey(spans, String(SYNTAX.sourcetext(index))) || !covers_dimension(spans[String(SYNTAX.sourcetext(index))], name, dimension, length(indices))
            return false
        end
    end
    return length(indices) == length(ranges) && allunique(SYNTAX.sourcetext.(indices)) && isempty(variable_reads(last(node_children(write)), name))
end

"""Whether the syntax `node` holds an early exit of its loop: `break`, `continue`, `return`."""
has_exit(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) in EXIT_KINDS || any(has_exit, node_children(node))

"""The `statements` from the first one that reads the variable `name` on, empty when none does."""
from_first_reader(statements::AbstractVector{SYNTAX.SyntaxNode}, name::String)::Vector{SYNTAX.SyntaxNode} = collect(Iterators.dropwhile(statement -> isempty(variable_reads(statement, name)), statements))

"""Whether the statement `later` writes the array `name` in full before any read: `name .= …`, or a loop over every index whose first statement to use `name` is `name[i, …] = …`."""
function initializes_array(later::SYNTAX.SyntaxNode, name::String, rank::Int)::Bool
    parts = node_children(later)
    if SYNTAX.kind(later) === BROADCAST_ASSIGN_KIND
        return is_identifier(first(parts), name) && isempty(variable_reads(last(parts), name))
    elseif SYNTAX.kind(later) !== SYNTAX.@K_str("for") || has_exit(later)
        return false
    end
    ranges = loop_ranges(later)
    body = last(parts)
    statements = node_children(body)
    used = from_first_reader(statements, name)
    if isempty(used) || length(ranges) != rank || length(ranges) != length(node_children(first(parts)))
        return false
    end
    return writes_every_index(first(used), name, ranges) && isempty(from_first_reader(used[2:end], name))
end

"""The number of dimensions the constructor `dimensions` texts give, or `0` when a tuple, a `size(…)` or a splat hides it."""
function constructor_rank(dimensions::AbstractVector{<:AbstractString})::Int
    hidden = any(text -> startswith(text, "(") || endswith(text, "...") || occursin(r"^size\([^,]*\)$", text), dimensions)
    return hidden ? 0 : length(dimensions)
end

"""The `NanInitializer` of the assignment `binding` of a constant-array call to a variable, as a vector that is empty when the array is never written, only accumulated, or its element type is unknown."""
function binding_initializers(binding::SYNTAX.SyntaxNode)::Vector{NanInitializer}
    target, call = node_children(binding)
    scopes = enclosing_scope(binding)
    parent = binding.parent
    if SYNTAX.kind(target) !== IDENTIFIER_KIND || !is_prefix_call(call) || isempty(scopes) || !is_statement(binding) || isnothing(parent) || SYNTAX.kind(parent) !== SYNTAX.@K_str("block")
        return NanInitializer[]
    end
    name = constructor_name(first(node_children(call)))
    arguments = filter(!keyword_part, node_children(call)[2:end])
    if !(name in ("zeros", "ones", "fill")) || isempty(arguments) || any(names_static_array, arguments)
        return NanInitializer[]
    end
    variable = String(SYNTAX.sourcetext(target))
    reads = filter(!Base.Fix1(===, target), variable_reads(only(scopes), variable))
    element, dimensions = element_and_dimensions(call, name)
    if isempty(reads) || element == UNTYPED_FILL || !any(Base.Fix1(===, :mutated) ∘ use_of, reads) || any(is_accumulation, reads)
        return NanInitializer[]
    end
    siblings = node_children(parent)
    later = from_first_reader(siblings[(only(findall(Base.Fix1(===, binding), siblings)) + 1):end], variable)
    proven = element != UNKNOWN_ELEMENT && !isempty(later) && initializes_array(first(later), variable, constructor_rank(dimensions))
    proof = element in NANLESS_TYPES ? :nanless : proven ? :initializer : :unproven
    return [NanInitializer(call, name, proof, element, dimensions, dimension_template(call, dimensions))]
end

"""Every written constant-array initializer below syntax `node`, in source order."""
function nan_initializers(node::SYNTAX.SyntaxNode)::Vector{NanInitializer}
    found = NanInitializer[]
    if SYNTAX.kind(node) === SYNTAX.@K_str("=") && length(node_children(node)) == 2
        append!(found, binding_initializers(node))
    end
    for child in node_children(node)
        append!(found, nan_initializers(child))
    end
    return found
end

"""The text of the NaN initializer that replaces `initializer`: `fill!(similar(template, T, dimensions…), NaN)` when an array in scope gives the dimensions, else `fill(T(NaN), dimensions…)` (`fill(NaN, dimensions…)` for Float64)."""
function nan_text(initializer::NanInitializer)::String
    element = isempty(initializer.element) ? "Float64" : initializer.element
    dimensions = join(initializer.dimensions, ", ")
    if !isempty(initializer.template)
        return "fill!(similar($(initializer.template), $element, $dimensions), NaN)"
    end
    return "fill($(isempty(initializer.element) ? "NaN" : element * "(NaN)"), $dimensions)"
end

"""The site of `initializer` in `source`, at its lines."""
function nan_initializer_site(source::Source, initializer::NanInitializer)::Site
    node = initializer.call
    first_line = first(SYNTAX.source_location(node))
    last_line = first(SYNTAX.source_location(node.source, last(SYNTAX.byte_range(node))))
    advice = if initializer.proof === :initializer
        "every element is written before it is read, so initialize with NaN: `$(nan_text(initializer))`"
    elseif initializer.proof === :nanless
        "an $(initializer.element) array has no NaN to show an untouched element; pick a sentinel by hand"
    else
        "the array is written but not provably in full before any read; initialize with NaN if no element is read as its start value"
    end
    return Site(source.name, source.path, first_line, last_line, "`$(initializer.name)` initializes an array that is then written; $advice")
end

"""One site per written array initialized with a constant (`nan_initializers`)."""
function nan_initializer_sites(sources::AbstractVector{Source})::Vector{Site}
    sites = Site[]
    for source in sources
        for initializer in nan_initializers(source.tree)
            push!(sites, nan_initializer_site(source, initializer))
        end
    end
    return sites
end

"""The repairs of `source`: one per proven initializer."""
function nan_initializer_repairs(source::Source)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for initializer in nan_initializers(source.tree)
        if initializer.proof === :initializer
            push!(repairs, Repair(nan_initializer_site(source, initializer), ByteRewrite(source.path, SYNTAX.byte_range(initializer.call), nan_text(initializer))))
        end
    end
    return repairs
end

"""
    nan_initializer_plan(repository, directories)

The `FixPlan` that rewrites each proven initializer `zeros(T, dims…)`, `ones(T, dims…)` or `fill(v, dims…)` as `fill(T(NaN), dims…)`, or `fill!(similar(x, T, dims…), NaN)` when `length(x)` or `size(x)` of an array in scope gives the dimensions. Two limits no check can exclude: a template built by `Array(y)` or `Vector(y)` from a sparse or device `y` keeps that type, and
so does a sparse `x`, so review the diff.
"""
function nan_initializer_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)}
    repairs = Repair{ByteRewrite}[]
    for source in directory_sources(repository, directories)
        append!(repairs, nan_initializer_repairs(source))
    end
    return FixPlan(repairs, rewritten_texts)
end

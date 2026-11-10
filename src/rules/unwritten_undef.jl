# The rule `unwritten-undef` and its fixer: an element no write reached must show. An uninitialized array (`similar(…)`,
# `T(undef, …)`) passes only when `initializes_array` proves every element written before any read; a written `zeros`,
# `ones` or `fill` array should start as NaN, and the fixer rewrites the proven ones as `fill(T(NaN), dims…)`.

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

# Calls that write every element of one argument, by its position, whatever the others hold.
const WHOLE_WRITERS = (; var"fill!" = 1, var"copy!" = 1, var"broadcast!" = 2, var"rand!" = 1, var"randn!" = 1, var"randexp!" = 1)

# How an initializer array is judged: `:initializer` (every element written before any read, fixable), `:unproven`
# (written, but not provably an initializer) or `:nanless` (an integer or Bool array, which has no NaN).
"""One constant-array constructor `call` (`zeros`, `ones` or `fill`) of an array that is written, with its `proof`, the `element` type text (`""` for Float64) and its `dimensions` text."""
struct NanInitializer
    call::SYNTAX.SyntaxNode
    name::String
    proof::Symbol
    element::String
    dimensions::Vector{String}
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

"""The `call_name` of call syntax `call` when it names its function bare or through `Base` or `Random`; `""` for a lookalike (`Custom.fill!`)."""
trusted_name(call::SYNTAX.SyntaxNode)::String = SYNTAX.kind(first(node_children(call))) === IDENTIFIER_KIND || occursin(r"^(Base|Random)\.\w+!?$", SYNTAX.sourcetext(first(node_children(call)))) ? call_name(call) : ""

"""Whether range syntax `range` runs over the whole of dimension `dimension` of the array `name` of `dimensions` dimensions."""
function covers_dimension(range::SYNTAX.SyntaxNode, name::String, dimension::Int, dimensions::Int)::Bool
    if SYNTAX.kind(range) === CALL_KIND && is_prefix_call(range)
        arguments = node_children(range)[2:end]
        called = trusted_name(range)
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

"""
Whether the statement `later` writes the array `name` of `rank` dimensions (`0` when unknown) in full before any read:
`name .= …`, a `WHOLE_WRITERS` call that passes `name` once, at its written position, or a loop over every index whose
first statement to use `name` is `name[i, …] = …` (`for i in eachindex(name)` whatever the rank).
"""
function initializes_array(later::SYNTAX.SyntaxNode, name::String, rank::Int)::Bool
    parts = node_children(later)
    if SYNTAX.kind(later) === BROADCAST_ASSIGN_KIND
        return is_identifier(first(parts), name) && isempty(variable_reads(last(parts), name))
    elseif is_prefix_call(later) && haskey(WHOLE_WRITERS, Symbol(trusted_name(later)))
        position = findfirst(Base.Fix2(is_identifier, name), filter(!keyword_part, parts[2:end]))
        return count(!isempty ∘ Base.Fix2(variable_reads, name), parts) == 1 && position == WHOLE_WRITERS[Symbol(trusted_name(later))]
    elseif SYNTAX.kind(later) !== SYNTAX.@K_str("for") || has_exit(later)
        return false
    end
    ranges = loop_ranges(later)
    body = last(parts)
    statements = node_children(body)
    used = from_first_reader(statements, name)
    linear = length(ranges) == 1 && is_prefix_call(last(only(ranges))) && trusted_name(last(only(ranges))) == "eachindex"
    if isempty(used) || !(length(ranges) == rank || (rank == 0 && linear)) || length(ranges) != length(node_children(first(parts))) || assigns_any(body, first.(ranges))
        return false
    end
    return writes_every_index(first(used), name, ranges) && isempty(from_first_reader(used[2:end], name))
end

"""Whether the first statement after the statement `binding` in its block to read the array `name` of `rank` dimensions is an `initializes_array` proof."""
function written_after(binding::SYNTAX.SyntaxNode, name::String, rank::Int)::Bool
    siblings = node_children(something(binding.parent))
    later = from_first_reader(siblings[(something(findfirst(Base.Fix1(===, binding), siblings)) + 1):end], name)
    scopes = enclosing_scope(binding)
    return !isempty(later) && initializes_array(first(later), name, rank) && (isempty(scopes) || !closure_reads(only(scopes), name))
end

"""Whether syntax `node` assigns a variable of `names` (`i = …`, `i += …`), so a loop variable may stop covering its range."""
assigns_any(node::SYNTAX.SyntaxNode, names::AbstractVector{String})::Bool =
    (SYNTAX.kind(node) in (SYNTAX.@K_str("="), SYNTAX.@K_str("op=")) && any(Base.Fix1(is_identifier, first(node_children(node))), names)) || any(Base.Fix2(assigns_any, names), node_children(node))

"""Whether a closure (`->`, `do` or an inner `function`) below syntax `node` reads `name`: a call may read the array before its write."""
closure_reads(node::SYNTAX.SyntaxNode, name::String)::Bool = any(Base.Fix2(reading_closure, name), node_children(node))

"""Whether syntax `node` is or holds a closure that reads `name` (`closure_reads`)."""
reading_closure(node::SYNTAX.SyntaxNode, name::String)::Bool =
    (SYNTAX.kind(node) in (SYNTAX.@K_str("->"), SYNTAX.@K_str("do"), SYNTAX.@K_str("function")) && !isempty(variable_reads(node, name))) || closure_reads(node, name)

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
    proven = element != UNKNOWN_ELEMENT && written_after(binding, variable, constructor_rank(dimensions))
    proof = element in NANLESS_TYPES ? :nanless : proven ? :initializer : :unproven
    return [NanInitializer(call, name, proof, element, dimensions)]
end

"""Every written constant-array initializer below syntax `node`, in source order."""
function nan_initializers(node::SYNTAX.SyntaxNode)::Vector{NanInitializer}
    bound = SYNTAX.kind(node) === SYNTAX.@K_str("=") && length(node_children(node)) == 2 ? binding_initializers(node) : NanInitializer[]
    return append!(bound, Iterators.flatten(nan_initializers.(node_children(node))))
end

"""The text of the NaN initializer that replaces `initializer`: `fill(T(NaN), dimensions…)`, or `fill(NaN, dimensions…)` for Float64."""
nan_text(initializer::NanInitializer)::String = "fill($(isempty(initializer.element) ? "NaN" : initializer.element * "(NaN)"), $(join(initializer.dimensions, ", ")))"

"""The site of call syntax `call` in `source`, at its lines, with `detail`."""
call_site(source::Source, call::SYNTAX.SyntaxNode, detail::String)::Site =
    Site(source.name, source.path, first(SYNTAX.source_location(call)), first(SYNTAX.source_location(call.source, last(SYNTAX.byte_range(call)))), detail)

"""The site of `initializer` in `source`, at its lines."""
function nan_initializer_site(source::Source, initializer::NanInitializer)::Site
    advice = if initializer.proof === :initializer
        "every element is written before it is read, so initialize with NaN: `$(nan_text(initializer))`"
    elseif initializer.proof === :nanless
        "an $(initializer.element) array has no NaN to show an untouched element; pick a sentinel by hand"
    else
        "the array is written but not provably in full before any read; initialize with NaN if no element is read as its start value"
    end
    return call_site(source, initializer.call, "`$(initializer.name)` initializes an array that is then written; $advice")
end

"""Whether call syntax `call` builds an uninitialized array: `similar(…)` or `T(undef, …)`, outside a method signature."""
function is_undef_call(call::SYNTAX.SyntaxNode)::Bool
    parts = node_children(call)
    return is_prefix_call(call) && !in_signature(call) && length(parts) > 1 &&
        (constructor_name(first(parts)) == "similar" || (names_type(first(parts)) && is_identifier(parts[2], "undef")))
end

"""
The number of dimensions the uninitialized array `call` gets, `0` when unknown: the dimensions it lists after `undef`
or after the element type of `similar(template, T, dims…)` (`constructor_rank`).
"""
function undef_rank(call::SYNTAX.SyntaxNode)::Int
    arguments = filter(!keyword_part, node_children(call)[2:end])
    listed = is_identifier(first(arguments), "undef") || names_type(first(arguments)) ? arguments[2:end] :
        length(arguments) > 1 && names_type(arguments[2]) ? arguments[3:end] : SYNTAX.SyntaxNode[]
    return isempty(listed) ? 0 : constructor_rank(String[SYNTAX.sourcetext(argument) for argument in listed])
end

"""
Whether the uninitialized array `call` is written in full before any read: passed straight to a whole-array writer
(`fill!(similar(x), NaN)`), or bound to a local whose first later statement to read it is an `initializes_array` proof.
"""
function undef_call_written(call::SYNTAX.SyntaxNode)::Bool
    parent = something(call.parent)
    if is_prefix_call(parent) && haskey(WHOLE_WRITERS, Symbol(trusted_name(parent)))
        return findfirst(Base.Fix1(===, call), filter(!keyword_part, node_children(parent)[2:end])) == WHOLE_WRITERS[Symbol(trusted_name(parent))]
    end
    target = first(node_children(parent))
    return SYNTAX.kind(parent) === SYNTAX.@K_str("=") && last(node_children(parent)) === call && SYNTAX.kind(target) === IDENTIFIER_KIND &&
        !isnothing(parent.parent) && SYNTAX.kind(parent.parent) === SYNTAX.@K_str("block") && written_after(parent, String(SYNTAX.sourcetext(target)), undef_rank(call))
end

"""Every uninitialized array call below syntax `node`, skipping quoted code and the methods of `similar`, which return one by contract."""
function undef_calls(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    if SYNTAX.kind(node) === SYNTAX.@K_str("quote") || (SYNTAX.kind(node) === SYNTAX.@K_str("function") && defined_name(Expr(node)) === :similar)
        return SYNTAX.SyntaxNode[]
    end
    return append!(is_undef_call(node) ? [node] : SYNTAX.SyntaxNode[], Iterators.flatten(undef_calls.(node_children(node))))
end

"""The site of the uninitialized array `call` of `source`, which `undef_call_written` cannot prove written in full."""
undef_site(source::Source, call::SYNTAX.SyntaxNode)::Site = call_site(
    source, call, "`$(SYNTAX.sourcetext(first(node_children(call))))` builds an array not provably written in full before it is read; " *
        "fill it (`fill!(similar(x, T), NaN)`) or write it whole first (`x .= …`, `fill!`, or a loop over `eachindex(x)` writing `x[i]`)"
)

"""One site per written constant-array initializer (`nan_initializers`) and per uninitialized array not provably written in full."""
function unwritten_undef_sites(sources::AbstractVector{Source})::Vector{Site}
    sites = Site[]
    for source in sources
        append!(sites, nan_initializer_site.((source,), nan_initializers(source.tree)), undef_site.((source,), filter(!undef_call_written, undef_calls(source.tree))))
    end
    return sites
end

"""The `FixPlan` that rewrites each proven initializer `zeros(T, dims…)`, `ones(T, dims…)` or `fill(v, dims…)` as `fill(T(NaN), dims…)`."""
function unwritten_undef_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)}
    repairs = Repair{ByteRewrite}[]
    for source in directory_sources(repository, directories), initializer in nan_initializers(source.tree)
        if initializer.proof === :initializer
            push!(repairs, Repair(nan_initializer_site(source, initializer), ByteRewrite(source.path, SYNTAX.byte_range(initializer.call), nan_text(initializer))))
        end
    end
    return FixPlan(repairs, rewritten_texts)
end

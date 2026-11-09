# The rule `constant-array` and its fixer: `zeros`, `ones`, `fill`, `trues` and `falses` build an array
# FillArrays.jl stores as one value. A FillArrays array is immutable, so only an array that is never
# written is a violation: a buffer that is written (`x[i] = …`, `x .= …`, a `!` call) stays silent.

# The FillArrays constructor that replaces each Base constructor.
const FILL_CONSTRUCTORS = (zeros = "Zeros", ones = "Ones", fill = "Fill", trues = "Trues", falses = "Falses")

# Base functions that only read their array arguments and return no array that aliases them.
const PURE_READERS = (
    "length", "size", "axes", "eachindex", "firstindex", "lastindex", "ndims", "sum", "prod", "maximum", "minimum",
    "extrema", "any", "all", "count", "first", "last", "isempty", "eltype", "dot", "norm", "iszero", "enumerate", "mean",
)

# `first` and `last` with a count return an array.
const SINGLE_ARGUMENT_READERS = ("first", "last")

# Constructors whose result is a mutable value: `fill` of one aliases it, so the call is no violation.
const MUTABLE_VALUES = ("Vector", "Matrix", "Array", "Dict", "Set", "Ref", "zeros", "ones", "fill", "similar", "copy", "collect", "trues", "falses")

# `zero(x)` of an array is a new array: these give a number only from a type.
const TYPE_ARGUMENT_NUMBERS = ("zero", "one", "oneunit")

# Functions that give a type.
const TYPE_FUNCTIONS = ("typeof", "eltype", "promote_type")

# Constructors and functions whose result is an immutable number.
const NUMBER_VALUES = (
    "typemax", "typemin", "Float16", "Float32", "Float64", "Int8", "Int16", "Int32", "Int64", "Int128",
    "UInt8", "UInt16", "UInt32", "UInt64", "UInt128", "Bool", "Complex", "ComplexF32", "ComplexF64", "Rational",
)

# StaticArrays types: `zeros(SVector{3})` and `fill(x, SVector{3})` build a static array, which FillArrays has no form for.
const STATIC_ARRAY_TYPES = ("SVector", "SMatrix", "SArray", "MVector", "MMatrix", "MArray", "SizedVector", "SizedMatrix", "SizedArray")

const LITERAL_KINDS = (SYNTAX.@K_str("Integer"), SYNTAX.@K_str("Float"), SYNTAX.@K_str("Float32"), SYNTAX.@K_str("Bool"), SYNTAX.@K_str("char"), SYNTAX.@K_str("string"))
const ASSIGN_KINDS = (SYNTAX.@K_str("="), SYNTAX.@K_str(".="), SYNTAX.@K_str("op="), SYNTAX.@K_str(".op="))
const SCOPE_KINDS = (SYNTAX.@K_str("function"), SYNTAX.@K_str("->"), SYNTAX.@K_str("let"), SYNTAX.@K_str("macro"))
const DISCARDING_KINDS = (SYNTAX.@K_str("for"), SYNTAX.@K_str("while"), SYNTAX.@K_str("module"))
const IMPORT_KINDS = (SYNTAX.@K_str("using"), SYNTAX.@K_str("import"))

# How a constant-array call is used, as a Symbol: `:safe` if no one writes the array, `:escape` if it leaves
# its function or is read in a way that may alias it, `:mutated` if it is written, `:ignored` if no FillArrays form fits.

"""One call of a Base constant-array constructor: its syntax `node`, the callee `name` and the `usage` of its result."""
struct ConstantArrayCall
    node::SYNTAX.SyntaxNode
    name::String
    usage::Symbol
end

"""The name `zeros` of callee syntax `callee` (`zeros` or `Base.zeros`), or `""` when it is neither."""
function constructor_name(callee::SYNTAX.SyntaxNode)::String
    parts = node_children(callee)
    if SYNTAX.kind(callee) === SYNTAX.@K_str(".") && length(parts) == 2 && !is_identifier(first(parts), "Base")
        return ""
    end
    return callee_name(callee)
end

"""The last name of callee syntax `callee`: `f` for `f` and `Mod.f`, `""` for anything else."""
function callee_name(callee::SYNTAX.SyntaxNode)::String
    if SYNTAX.kind(callee) === IDENTIFIER_KIND
        return SYNTAX.sourcetext(callee)
    elseif SYNTAX.kind(callee) === SYNTAX.@K_str(".") && !isempty(node_children(callee)) && SYNTAX.kind(last(node_children(callee))) === IDENTIFIER_KIND
        return SYNTAX.sourcetext(last(node_children(callee)))
    end
    return ""
end

"""Whether call syntax `node` is the prefix call `f(…)`, not an infix, postfix or dotted call."""
is_prefix_call(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) === CALL_KIND && SYNTAX.is_prefix_call(node)

"""Whether syntax `node` is the signature of a method definition, below any `where` or return annotation."""
function in_signature(node::SYNTAX.SyntaxNode)::Bool
    parent = node.parent
    while !isnothing(parent) && SYNTAX.kind(parent) in (SYNTAX.@K_str("where"), SYNTAX.@K_str("::")) && first(node_children(parent)) === node
        node = parent
        parent = node.parent
    end
    return !isnothing(parent) && SYNTAX.kind(parent) === SYNTAX.@K_str("function") && first(node_children(parent)) === node
end

"""The callee name of call syntax `node`, with a trailing `!` kept; infix calls name their operator."""
function call_name(node::SYNTAX.SyntaxNode)::String
    parts = node_children(node)
    return callee_name(SYNTAX.is_infix_op_call(node) ? parts[2] : first(parts))
end

"""Whether `node` is a direct argument of its call parent `parent`, not the callee."""
is_argument(node::SYNTAX.SyntaxNode, parent::SYNTAX.SyntaxNode)::Bool = !SYNTAX.is_prefix_call(parent) || first(node_children(parent)) !== node

"""Whether syntax `node` is an integer literal or `end`: a name may hold a vector, so it is no scalar."""
is_scalar_operand(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) === SYNTAX.@K_str("Integer") || is_identifier(node, "end")

"""Whether `index` is a scalar operand or a sum or difference of two."""
function is_scalar_index(index::SYNTAX.SyntaxNode)::Bool
    parts = node_children(index)
    if SYNTAX.kind(index) === CALL_KIND && length(parts) == 3 && call_name(index) in ("+", "-")
        return is_scalar_operand(parts[1]) && is_scalar_operand(parts[3])
    end
    return is_scalar_operand(index)
end

"""Whether every index of `reference`, a `ref` node, is an integer literal, `end` or a sum of them: the read gives an element, not a slice."""
scalar_index(reference::SYNTAX.SyntaxNode)::Bool = all(is_scalar_index, node_children(reference)[2:end])

"""Whether a view macro (`@view`, `@views`) encloses syntax `node`."""
function in_view_macro(node::SYNTAX.SyntaxNode)::Bool
    parent = node.parent
    while !isnothing(parent)
        if SYNTAX.kind(parent) === SYNTAX.@K_str("macrocall") && lstrip(SYNTAX.sourcetext(first(node_children(parent))), '@') in ("view", "views")
            return true
        end
        parent = parent.parent
    end
    return false
end

"""Whether the broadcast macro `@.` encloses syntax `node`."""
function in_dot_macro(node::SYNTAX.SyntaxNode)::Bool
    parent = node.parent
    while !isnothing(parent)
        if SYNTAX.kind(parent) === SYNTAX.@K_str("macrocall") && lstrip(SYNTAX.sourcetext(first(node_children(parent))), '@') == "."
            return true
        end
        parent = parent.parent
    end
    return false
end

"""Whether syntax `node` is assigned to: the target of an assignment, alone or inside a destructuring tuple."""
function is_assigned(node::SYNTAX.SyntaxNode)::Bool
    while !isnothing(node.parent) && SYNTAX.kind(node.parent) === SYNTAX.@K_str("tuple")
        node = node.parent
    end
    parent = node.parent
    return !isnothing(parent) && SYNTAX.kind(parent) in ASSIGN_KINDS && first(node_children(parent)) === node
end

"""Whether the call syntax `call` of the function `name` returns a scalar: a reader of the list, without keywords such as `dims`, and `first`/`last` without a count."""
function reads_only(call::SYNTAX.SyntaxNode, name::String)::Bool
    arguments = node_children(call)[2:end]
    return name in PURE_READERS && !any(keyword_part, arguments) && !(name in SINGLE_ARGUMENT_READERS && length(arguments) > 1)
end

"""How the array that syntax `node` holds (the call itself, or an occurrence of the name it is bound to) is used, judged by its parent."""
function use_of(node::SYNTAX.SyntaxNode)::Symbol
    parent = something(node.parent)
    kind = SYNTAX.kind(parent)
    parts = node_children(parent)
    if kind === SYNTAX.@K_str("ref") && first(parts) === node
        if is_assigned(parent)
            return :mutated
        end
        return !in_view_macro(parent) && scalar_index(parent) ? :safe : :escape
    elseif kind in ASSIGN_KINDS && first(parts) === node
        if kind in (SYNTAX.@K_str(".="), SYNTAX.@K_str(".op=")) || (kind in (SYNTAX.@K_str("="), SYNTAX.@K_str("op=")) && in_dot_macro(parent))
            return :mutated
        end
        return kind === SYNTAX.@K_str("=") ? :safe : :escape
    elseif kind in (CALL_KIND, SYNTAX.@K_str("dotcall")) && is_argument(node, parent)
        name = call_name(parent)
        if endswith(name, "!")
            return :mutated
        end
        return kind === CALL_KIND && reads_only(parent, name) ? :safe : :escape
    elseif kind === SYNTAX.@K_str("in") && last(parts) === node && SYNTAX.kind(parent.parent) === SYNTAX.@K_str("iteration")
        return :safe
    end
    return :escape
end

"""The nearest function, lambda, `let` or macro definition around syntax `node`, as a vector of one node, or of none at the top level."""
function enclosing_scope(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    parent = node.parent
    while !isnothing(parent) && !(SYNTAX.kind(parent) in SCOPE_KINDS)
        parent = parent.parent
    end
    return isnothing(parent) ? SYNTAX.SyntaxNode[] : [parent]
end

"""Whether the child at `position` of `node` is no read of a variable: a field name `a.name` or a keyword name `f(name = …)`."""
function names_no_variable(node::SYNTAX.SyntaxNode, position::Int)::Bool
    if SYNTAX.kind(node) === SYNTAX.@K_str(".")
        return position == 2
    end
    return SYNTAX.kind(node) === KEYWORD_KIND && position == 1 && !isnothing(node.parent) && SYNTAX.kind(node.parent) in (CALL_KIND, PARAMETERS_KIND)
end

"""Every identifier below syntax `node` named `name` that reads the variable: not a field name `a.name` nor a keyword name `f(name = …)`."""
function variable_reads(node::SYNTAX.SyntaxNode, name::String)::Vector{SYNTAX.SyntaxNode}
    parts = node_children(node)
    reads = SYNTAX.SyntaxNode[]
    if isempty(parts) && is_identifier(node, name)
        push!(reads, node)
    end
    for (position, part) in enumerate(parts)
        if !names_no_variable(node, position)
            append!(reads, variable_reads(part, name))
        end
    end
    return reads
end

"""The most severe of `usages`: `:mutated`, then `:escape`, then `:safe`."""
function worst_usage(usages::AbstractVector{Symbol})::Symbol
    for severity in (:mutated, :escape)
        if severity in usages
            return severity
        end
    end
    return :safe
end

"""The usage of the variable `name` that `binding` assigns, over every read of `name` in `scope`."""
function variable_usage(scope::SYNTAX.SyntaxNode, name::String, binding::SYNTAX.SyntaxNode)::Symbol
    target = first(node_children(binding))
    usages = Symbol[]
    for read in variable_reads(scope, name)
        if read !== target
            push!(usages, use_of(read))
        end
    end
    return worst_usage(usages)
end

"""Whether assignment `binding` is a statement that discards its value: a block child that is not a function's result."""
function is_statement(binding::SYNTAX.SyntaxNode)::Bool
    parent = binding.parent
    while !isnothing(parent) && SYNTAX.kind(parent) === SYNTAX.@K_str("local")
        binding = parent
        parent = parent.parent
    end
    if isnothing(parent) || SYNTAX.kind(parent) !== SYNTAX.@K_str("block")
        return !isnothing(parent) && SYNTAX.kind(parent) === SYNTAX.@K_str("toplevel")
    end
    # The last statement of any other block (`if`, `try`, `begin`) may be the function's value.
    return last(node_children(parent)) !== binding || (!isnothing(parent.parent) && SYNTAX.kind(parent.parent) in DISCARDING_KINDS)
end

"""The field and variable names some code writes through (`name[…] = …`, `name .= …`, `f!(name)`)."""
struct WrittenNames
    fields::Set{String}
    variables::Set{String}
end

"""Whether some code writes through `name`, as a field or as a variable."""
is_written(written::WrittenNames, name::String)::Bool = name in written.fields || name in written.variables

"""The name an entry `name = call` (a keyword argument or a named-tuple entry) gives the call syntax `call`, or `""` when `call` is no such entry."""
function entry_name(call::SYNTAX.SyntaxNode)::String
    entry = call.parent
    if isnothing(entry) || SYNTAX.kind(entry) !== KEYWORD_KIND || last(node_children(entry)) !== call || isnothing(entry.parent)
        return ""
    elseif !(SYNTAX.kind(entry.parent) in (CALL_KIND, PARAMETERS_KIND, SYNTAX.@K_str("tuple"))) || SYNTAX.kind(first(node_children(entry))) !== IDENTIFIER_KIND
        return ""
    end
    return String(SYNTAX.sourcetext(first(node_children(entry))))
end

"""
The usage of the array that call syntax `call` builds: the entry or variable it is bound to, read in its scope, or else
the call's own parent. An array that escapes under a field or entry name some code writes through, or a local name some
code writes through as a field, counts as written.
"""
function call_usage(call::SYNTAX.SyntaxNode, written::WrittenNames)::Symbol
    named = entry_name(call)
    binding = call.parent
    if !isempty(named)
        return is_written(written, named) ? :mutated : use_of(call)
    elseif isnothing(binding) || SYNTAX.kind(binding) !== SYNTAX.@K_str("=") || last(node_children(binding)) !== call || SYNTAX.kind(binding.parent) in (CALL_KIND, PARAMETERS_KIND)
        return use_of(call)
    end
    target = first(node_children(binding))
    scopes = enclosing_scope(binding)
    if SYNTAX.kind(target) === SYNTAX.@K_str("::")
        return :ignored
    elseif SYNTAX.kind(target) === SYNTAX.@K_str(".")
        return is_written(written, callee_name(target)) ? :mutated : :escape
    elseif SYNTAX.kind(target) !== IDENTIFIER_KIND || isempty(scopes) || !is_statement(binding)
        return :escape
    end
    name = String(SYNTAX.sourcetext(target))
    usage = variable_usage(only(scopes), name, binding)
    return usage === :escape && name in written.fields ? :mutated : usage
end

"""Whether syntax `argument` names a type: a capitalized name, a parametric type, or `typeof(…)`, `eltype(…)`, `promote_type(…)`."""
function names_type(argument::SYNTAX.SyntaxNode)::Bool
    if SYNTAX.kind(argument) === SYNTAX.@K_str("curly")
        return true
    elseif SYNTAX.kind(argument) === CALL_KIND
        return is_prefix_call(argument) && call_name(argument) in TYPE_FUNCTIONS
    end
    name = callee_name(argument)
    return !isempty(name) && isuppercase(first(name))
end

"""Whether the value syntax `value` of a `fill` is `:number` (immutable), `:mutable` (aliased by `fill`, so left alone) or `:unknown`."""
function fill_value_kind(value::SYNTAX.SyntaxNode)::Symbol
    kind = SYNTAX.kind(value)
    if kind in LITERAL_KINDS || (kind === IDENTIFIER_KIND && SYNTAX.sourcetext(value) in ("nothing", "missing", "NaN", "NaN32", "Inf", "Inf32"))
        return :number
    elseif kind in (SYNTAX.@K_str("vect"), SYNTAX.@K_str("comprehension"), SYNTAX.@K_str("generator"), SYNTAX.@K_str("ref"), SYNTAX.@K_str("braces"))
        return :mutable
    elseif kind === CALL_KIND && is_prefix_call(value)
        head = first(node_children(value))
        name = SYNTAX.kind(head) === SYNTAX.@K_str("curly") ? constructor_name(first(node_children(head))) : constructor_name(head)
        if name in TYPE_ARGUMENT_NUMBERS
            return length(node_children(value)) == 2 && names_type(node_children(value)[2]) ? :number : :unknown
        end
        return name in MUTABLE_VALUES ? :mutable : name in NUMBER_VALUES ? :number : :unknown
    end
    return :unknown
end

"""The name of the array syntax `node` holds: a variable, or the last field of `a.b.name`; `""` for anything else."""
array_name(node::SYNTAX.SyntaxNode)::String = SYNTAX.kind(node) in (IDENTIFIER_KIND, SYNTAX.@K_str(".")) ? callee_name(node) : ""

"""The names below syntax `node` that some code writes through, as `:field => name` or `:variable => name`."""
function written_names(node::SYNTAX.SyntaxNode)::Vector{Pair{Symbol, String}}
    names = Pair{Symbol, String}[]
    for child in node_children(node)
        append!(names, written_names(child))
    end
    name = array_name(node)
    if !isempty(name) && !isnothing(node.parent) && use_of(node) === :mutated
        push!(names, (SYNTAX.kind(node) === IDENTIFIER_KIND ? :variable : :field) => name)
    end
    return names
end

"""Every call of a Base constant-array constructor under syntax `node`, with the usage of its result, in source order."""
function constant_array_calls(node::SYNTAX.SyntaxNode, written::WrittenNames)::Vector{ConstantArrayCall}
    found = ConstantArrayCall[]
    for child in node_children(node)
        append!(found, constant_array_calls(child, written))
    end
    if !is_prefix_call(node) || in_signature(node)
        return found
    end
    name = constructor_name(first(node_children(node)))
    arguments = filter(!keyword_part, node_children(node)[2:end])
    if !(Symbol(name) in keys(FILL_CONSTRUCTORS)) || (name == "fill" && isempty(arguments)) || any(names_static_array, arguments)
        return found
    end
    usage = call_usage(node, written)
    if name == "fill"
        value = fill_value_kind(first(arguments))
        usage = value === :mutable ? :ignored : value === :unknown && usage === :safe ? :escape : usage
    end
    return usage in (:safe, :escape) ? vcat([ConstantArrayCall(node, name, usage)], found) : found
end

"""Whether syntax `argument` names a StaticArrays type, bare or with parameters."""
function names_static_array(argument::SYNTAX.SyntaxNode)::Bool
    if SYNTAX.kind(argument) === SYNTAX.@K_str("curly")
        return names_static_array(first(node_children(argument)))
    end
    return callee_name(argument) in STATIC_ARRAY_TYPES
end

"""The site of the constant-array `call` in `source`, at its lines."""
function constant_array_site(source::Source, call::ConstantArrayCall)::Site
    first_line = first(SYNTAX.source_location(call.node))
    last_line = first(SYNTAX.source_location(call.node.source, last(SYNTAX.byte_range(call.node))))
    advice = call.usage === :safe ? "never written" : "may be written elsewhere (check by hand: Corset rewrites no array that leaves its function)"
    return Site(source.name, source.path, first_line, last_line, "`$(call.name)` builds an array FillArrays stores as one value; $advice, so use `$(FILL_CONSTRUCTORS[Symbol(call.name)])`")
end

"""One constant-array site per call whose result no code writes (`constant_array_calls`): a written array has no FillArrays form."""
function constant_array_sites(sources::AbstractVector{Source})::Vector{Site}
    written = written_in(sources)
    sites = Site[]
    for source in sources
        for call in constant_array_calls(source.tree, written)
            push!(sites, constant_array_site(source, call))
        end
    end
    return sites
end

"""The names some file of `sources` writes through (`written_names`)."""
function written_in(sources::AbstractVector{Source})::WrittenNames
    written = WrittenNames(Set{String}(), Set{String}())
    for source in sources
        for (kind, name) in written_names(source.tree)
            push!(kind === :field ? written.fields : written.variables, name)
        end
    end
    return written
end

"""The FillArrays `constructor` that replaces the callee at the bytes `range` of the file `path`."""
struct FillRewrite
    path::String
    range::UnitRange{Int}
    constructor::String
end

"""The repairs of the Julia file `source`: one per constant-array call whose array no code writes or passes on."""
function constant_array_repairs(source::Source, written::WrittenNames)::Vector{Repair{FillRewrite}}
    repairs = Repair{FillRewrite}[]
    for call in constant_array_calls(source.tree, written)
        if call.usage === :safe
            push!(repairs, Repair(constant_array_site(source, call), FillRewrite(source.path, SYNTAX.byte_range(first(node_children(call.node))), FILL_CONSTRUCTORS[Symbol(call.name)])))
        end
    end
    return repairs
end

"""The names `statement`, a `using` or `import`, brings in from FillArrays: its imported names, or `["*"]` for a bare `using FillArrays`."""
function fill_arrays_names(statement::SYNTAX.SyntaxNode)::Vector{String}
    names = String[]
    for part in node_children(statement)
        if SYNTAX.kind(part) === SYNTAX.@K_str(":") && SYNTAX.sourcetext(first(node_children(first(node_children(part))))) == "FillArrays"
            append!(names, SYNTAX.sourcetext.(last.(node_children.(node_children(part)[2:end]))))
        elseif SYNTAX.kind(statement) === SYNTAX.@K_str("using") && SYNTAX.kind(part) === SYNTAX.@K_str("importpath") && is_identifier(first(node_children(part)), "FillArrays")
            push!(names, "*")
        end
    end
    return names
end

"""Every `using` and `import` statement of the scope `node`, a file or a module body, outside functions and nested modules, in source order."""
function import_statements(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    if SYNTAX.kind(node) in IMPORT_KINDS
        return [node]
    elseif SYNTAX.kind(node) in (SYNTAX.@K_str("toplevel"), SYNTAX.@K_str("block"))
        return SYNTAX.SyntaxNode[found for child in node_children(node) for found in import_statements(child)]
    end
    return SYNTAX.SyntaxNode[]
end

"""The import scope of the byte `offset` below syntax `node`: the body of the innermost module around it, else `scope`, the file."""
function import_scope(node::SYNTAX.SyntaxNode, offset::Int, scope::SYNTAX.SyntaxNode)::SYNTAX.SyntaxNode
    for child in node_children(node)
        if offset in SYNTAX.byte_range(child)
            return import_scope(child, offset, SYNTAX.kind(child) === SYNTAX.@K_str("module") ? last(node_children(child)) : scope)
        end
    end
    return scope
end

"""The edit that imports the FillArrays `constructors` the import `scope` of a file `text` uses but does not import: after its last import, or at its start."""
function import_edit(path::String, text::AbstractString, scope::SYNTAX.SyntaxNode, constructors::AbstractVector{String})::Vector{ByteRewrite}
    statements = import_statements(scope)
    imported = collect(String, Iterators.flatten(fill_arrays_names.(statements)))
    missing_names = sort!(setdiff(unique(constructors), imported))
    if "*" in imported || isempty(missing_names)
        return ByteRewrite[]
    end
    line = "using FillArrays: " * join(missing_names, ", ")
    if isempty(statements) && SYNTAX.kind(scope) === SYNTAX.@K_str("toplevel")
        # A shebang line must stay the first line of the file.
        start = startswith(text, "#!") ? something(findfirst('\n', text), ncodeunits(text)) + 1 : 1
        return [ByteRewrite(path, start:(start - 1), line * "\n\n")]
    elseif isempty(statements)
        first_statement = first(node_children(scope))
        start = first(SYNTAX.byte_range(first_statement))
        indent = match(r"^ *", split(text, '\n')[first(SYNTAX.source_location(first_statement))]).match
        return [ByteRewrite(path, start:(start - 1), line * "\n" * indent)]
    end
    last_statement = last(statements)
    indent = match(r"^ *", split(text, '\n')[first(SYNTAX.source_location(last_statement))]).match
    return [ByteRewrite(path, (last(SYNTAX.byte_range(last_statement)) + 1):last(SYNTAX.byte_range(last_statement)), "\n" * indent * line)]
end

"""The text of the file `path` with the callee `edits` made and the FillArrays names they use imported into the module each sits in."""
function filled_file(edits::AbstractVector{FillRewrite}, path::String)::Pair{String, String}
    own = edits[[edit.path for edit in edits] .== path]
    text = read(path, String)
    root = SYNTAX.parseall(SYNTAX.SyntaxNode, text)
    scopes = SYNTAX.SyntaxNode[]
    rewrites = ByteRewrite[]
    for edit in own
        push!(scopes, import_scope(root, first(edit.range), root))
        push!(rewrites, ByteRewrite(path, edit.range, edit.constructor))
    end
    for scope in unique(SYNTAX.byte_range, scopes)
        used = String[]
        for (edit, other) in zip(own, scopes)
            if SYNTAX.byte_range(other) == SYNTAX.byte_range(scope)
                push!(used, edit.constructor)
            end
        end
        append!(rewrites, import_edit(path, text, scope, used))
    end
    return path => rewritten(text, rewrites)
end

const FILL_ARRAYS_UUID = "1a297f60-69ca-5386-bcde-b61e274b549b"

"""The `[deps]` table of the Project.toml `text`, empty without one."""
function project_deps(text::AbstractString)::Dict{String, Any}
    return haskey(TOML.parse(text), "deps") ? TOML.parse(text)["deps"]::Dict{String, Any} : Dict{String, Any}() # lint: abstract-element  TOML tables hold values of every type
end

"""The Project.toml above the file `path`, as path => text, with FillArrays added to its `[deps]`; empty when it lists FillArrays already or no project exists."""
function dependency_file(path::String)::Vector{Pair{String, String}}
    directory = dirname(path)
    while !isfile(joinpath(directory, "Project.toml")) && dirname(directory) != directory
        directory = dirname(directory)
    end
    project = joinpath(directory, "Project.toml")
    if !isfile(project)
        return Pair{String, String}[]
    end
    text = read(project, String)
    if haskey(project_deps(text), "FillArrays")
        return Pair{String, String}[]
    end
    line = "FillArrays = \"$FILL_ARRAYS_UUID\"\n"
    text = endswith(text, "\n") ? text : text * "\n"
    added = occursin(r"(?m)^\[deps\][^\n]*\n", text) ? replace(text, r"(?m)^(\[deps\][^\n]*\n)" => SubstitutionString("\\1" * line); count = 1) : text * "\n[deps]\n" * line
    if !haskey(project_deps(added), "FillArrays")
        throw(ArgumentError("cannot list FillArrays in the [deps] of $project; add it by hand"))
    end
    return [project => added]
end

"""The new text of each file `edits` touch, as path => text, with FillArrays added to the Project.toml above each."""
function filled_texts(edits::AbstractVector{FillRewrite})::Vector{Pair{String, String}}
    paths = unique(String[edit.path for edit in edits])
    return vcat(filled_file.((edits,), paths), unique(first, Iterators.flatten(dependency_file.(paths))))
end

"""
    constant_array_plan(repository, directories)

The `FixPlan` that writes `zeros`, `ones`, `fill`, `trues` and `falses` calls of `directories` as `Zeros`, `Ones`,
`Fill`, `Trues` and `Falses`, imports those names from FillArrays into each module and lists FillArrays in the
Project.toml `[deps]`. A call is repaired only when no code writes the array and it never leaves its function: an array passed to
a call (as an argument or keyword), returned or stored may be written by the callee, so the rule only reports it.
"""
function constant_array_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{FillRewrite, typeof(filled_texts)}
    sources = directory_sources(repository, directories)
    written = written_in(sources)
    repairs = Repair{FillRewrite}[]
    for source in sources
        append!(repairs, constant_array_repairs(source, written))
    end
    return FixPlan(repairs, filled_texts)
end

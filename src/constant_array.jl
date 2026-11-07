# The rule `constant-array` and its fixer: `zeros`, `ones`, `fill`, `trues` and `falses` build an array
# FillArrays.jl stores as one value. A FillArrays array is immutable, so only an array that is never
# written is a violation: a buffer that is written (`x[i] = …`, `x .= …`, a `!` call) stays silent.

# The FillArrays constructor that replaces each Base constructor.
const FILL_CONSTRUCTORS = (zeros = "Zeros", ones = "Ones", fill = "Fill", trues = "Trues", falses = "Falses")

# Base functions that only read their array arguments and return no array that aliases them.
const PURE_READERS = (
    "length", "size", "axes", "eachindex", "firstindex", "lastindex", "ndims", "sum", "prod", "maximum", "minimum",
    "extrema", "any", "all", "count", "first", "last", "isempty", "eltype", "dot", "norm", "iszero", "enumerate",
)

# Constructors whose result is a mutable value: `fill` of one aliases it, so the call is no violation.
const MUTABLE_VALUES = ("Vector", "Matrix", "Array", "Dict", "Set", "Ref", "zeros", "ones", "fill", "similar", "copy", "collect", "trues", "falses")

# Constructors and functions whose result is an immutable number.
const NUMBER_VALUES = (
    "zero", "one", "oneunit", "typemax", "typemin", "Float16", "Float32", "Float64", "Int8", "Int16", "Int32", "Int64", "Int128",
    "UInt8", "UInt16", "UInt32", "UInt64", "UInt128", "Bool", "Complex", "ComplexF32", "ComplexF64", "Rational",
)

const LITERAL_KINDS = (SYNTAX.@K_str("Integer"), SYNTAX.@K_str("Float"), SYNTAX.@K_str("Float32"), SYNTAX.@K_str("Bool"), SYNTAX.@K_str("char"), SYNTAX.@K_str("string"))
const ASSIGN_KINDS = (SYNTAX.@K_str("="), SYNTAX.@K_str(".="), SYNTAX.@K_str("op="), SYNTAX.@K_str(".op="))
const SCOPE_KINDS = (SYNTAX.@K_str("function"), SYNTAX.@K_str("->"), SYNTAX.@K_str("let"), SYNTAX.@K_str("macro"))
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
    elseif SYNTAX.kind(callee) === SYNTAX.@K_str(".") && SYNTAX.kind(last(node_children(callee))) === IDENTIFIER_KIND
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

"""Whether syntax `node` is a number, a name or `end`."""
is_scalar_operand(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) in (SYNTAX.@K_str("Integer"), IDENTIFIER_KIND, SYNTAX.@K_str("end"))

"""Whether `index` is a scalar operand or a sum or difference of two."""
function is_scalar_index(index::SYNTAX.SyntaxNode)::Bool
    parts = node_children(index)
    if SYNTAX.kind(index) === CALL_KIND && length(parts) == 3 && call_name(index) in ("+", "-")
        return is_scalar_operand(parts[1]) && is_scalar_operand(parts[3])
    end
    return is_scalar_operand(index)
end

"""Whether every index of `reference`, a `ref` node, is a number, a name, `end` or a sum of them: the read gives an element, not a slice."""
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

"""How the array that syntax `node` holds (the call itself, or an occurrence of the name it is bound to) is used, judged by its parent."""
function use_of(node::SYNTAX.SyntaxNode)::Symbol
    parent = node.parent
    if isnothing(parent)
        return :escape
    end
    kind = SYNTAX.kind(parent)
    parts = node_children(parent)
    if kind === SYNTAX.@K_str("ref") && first(parts) === node
        grand = parent.parent
        if !isnothing(grand) && SYNTAX.kind(grand) in ASSIGN_KINDS && first(node_children(grand)) === parent
            return :mutated
        end
        return !in_view_macro(parent) && scalar_index(parent) ? :safe : :escape
    elseif kind in ASSIGN_KINDS && first(parts) === node
        if kind in (SYNTAX.@K_str(".="), SYNTAX.@K_str(".op=")) || (kind === SYNTAX.@K_str("=") && in_dot_macro(parent))
            return :mutated
        end
        return kind === SYNTAX.@K_str("=") ? :safe : :escape
    elseif kind in (CALL_KIND, SYNTAX.@K_str("dotcall")) && is_argument(node, parent)
        name = call_name(parent)
        if endswith(name, "!")
            return :mutated
        end
        return kind === CALL_KIND && name in PURE_READERS ? :safe : :escape
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
    return last(node_children(parent)) !== binding || isnothing(parent.parent) || !(SYNTAX.kind(parent.parent) in (SCOPE_KINDS..., SYNTAX.@K_str("do")))
end

"""The usage of the array that call syntax `call` builds: the variable it is bound to, read in its scope, or else the call's own parent."""
function call_usage(call::SYNTAX.SyntaxNode)::Symbol
    binding = call.parent
    if isnothing(binding) || SYNTAX.kind(binding) !== SYNTAX.@K_str("=") || last(node_children(binding)) !== call || SYNTAX.kind(binding.parent) in (CALL_KIND, PARAMETERS_KIND)
        return use_of(call)
    end
    target = first(node_children(binding))
    scopes = enclosing_scope(binding)
    if SYNTAX.kind(target) === SYNTAX.@K_str("::")
        return :ignored
    elseif SYNTAX.kind(target) !== IDENTIFIER_KIND || isempty(scopes) || !is_statement(binding)
        return :escape
    end
    return variable_usage(only(scopes), String(SYNTAX.sourcetext(target)), binding)
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
        return name in MUTABLE_VALUES ? :mutable : name in NUMBER_VALUES ? :number : :unknown
    end
    return :unknown
end

"""Every call of a Base constant-array constructor under syntax `node`, with the usage of its result, in source order."""
function constant_array_calls(node::SYNTAX.SyntaxNode)::Vector{ConstantArrayCall}
    found = ConstantArrayCall[found for child in node_children(node) for found in constant_array_calls(child)]
    if !is_prefix_call(node) || in_signature(node)
        return found
    end
    name = constructor_name(first(node_children(node)))
    arguments = filter(!keyword_part, node_children(node)[2:end])
    if !(Symbol(name) in keys(FILL_CONSTRUCTORS)) || (name == "fill" && isempty(arguments))
        return found
    end
    usage = call_usage(node)
    if name == "fill"
        value = fill_value_kind(first(arguments))
        usage = value === :mutable ? :ignored : value === :unknown && usage === :safe ? :escape : usage
    end
    return usage in (:safe, :escape) ? vcat([ConstantArrayCall(node, name, usage)], found) : found
end

"""The site of the constant-array `call` in `source`, at its lines."""
function constant_array_site(source::Source, call::ConstantArrayCall)::Site
    first_line = first(SYNTAX.source_location(call.node))
    last_line = first(SYNTAX.source_location(call.node.source, last(SYNTAX.byte_range(call.node))))
    advice = call.usage === :safe ? "never written" : "may be written elsewhere (fix with --unsafe-fixes)"
    return Site(source.name, source.path, first_line, last_line, "`$(call.name)` builds an array FillArrays stores as one value; $advice, so use `$(FILL_CONSTRUCTORS[Symbol(call.name)])`")
end

"""One constant-array site per call whose result no code writes (`constant_array_calls`): a written array has no FillArrays form."""
constant_array_sites(source::Source)::Vector{Site} = constant_array_site.((source,), constant_array_calls(source.tree))

"""The FillArrays `constructor` that replaces the callee at the bytes `range` of the file `path`."""
struct FillRewrite
    path::String
    range::UnitRange{Int}
    constructor::String
end

"""The repairs of the Julia file `source`: one per constant-array call, the `:escape` ones too when `unsafe`."""
function constant_array_repairs(source::Source, unsafe::Bool)::Vector{Repair{FillRewrite}}
    calls = filter(call -> call.usage === :safe || unsafe, constant_array_calls(source.tree))
    return Repair{FillRewrite}[
        Repair(constant_array_site(source, call), FillRewrite(source.path, SYNTAX.byte_range(first(node_children(call.node))), FILL_CONSTRUCTORS[Symbol(call.name)]))
            for call in calls
    ]
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

"""Every `using` and `import` statement under syntax `node` outside function bodies, in source order."""
function import_statements(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    if SYNTAX.kind(node) in IMPORT_KINDS
        return [node]
    elseif SYNTAX.kind(node) in (SYNTAX.@K_str("toplevel"), SYNTAX.@K_str("module"), SYNTAX.@K_str("block"))
        return SYNTAX.SyntaxNode[found for child in node_children(node) for found in import_statements(child)]
    end
    return SYNTAX.SyntaxNode[]
end

"""The edit that imports the FillArrays `constructors` a file `text` uses but does not import: after its last import, or at its start."""
function import_edit(path::String, text::AbstractString, constructors::AbstractVector{String})::Vector{ByteRewrite}
    statements = import_statements(SYNTAX.parseall(SYNTAX.SyntaxNode, text))
    imported = collect(String, Iterators.flatten(fill_arrays_names.(statements)))
    missing_names = sort!(setdiff(unique(constructors), imported))
    if "*" in imported || isempty(missing_names)
        return ByteRewrite[]
    end
    line = "using FillArrays: " * join(missing_names, ", ")
    if isempty(statements)
        return [ByteRewrite(path, 1:0, line * "\n\n")]
    end
    last_statement = last(statements)
    indent = match(r"^ *", split(text, '\n')[first(SYNTAX.source_location(last_statement))]).match
    return [ByteRewrite(path, (last(SYNTAX.byte_range(last_statement)) + 1):last(SYNTAX.byte_range(last_statement)), "\n" * indent * line)]
end

"""The text of the file `path` with the callee `edits` made and the FillArrays names they use imported."""
function filled_file(edits::AbstractVector{FillRewrite}, path::String)::Pair{String, String}
    own = edits[[edit.path for edit in edits] .== path]
    text = read(path, String)
    callees = ByteRewrite[ByteRewrite(path, edit.range, edit.constructor) for edit in own]
    return path => rewritten(text, vcat(callees, import_edit(path, text, [edit.constructor for edit in own])))
end

"""The new text of each file `edits` touch, as path => text."""
filled_texts(edits::AbstractVector{FillRewrite})::Vector{Pair{String, String}} = filled_file.((edits,), unique(String[edit.path for edit in edits]))

"""
    constant_array_plan(repository, directories, unsafe)

The `FixPlan` that writes `zeros`, `ones`, `fill`, `trues` and `falses` calls of `directories` as `Zeros`, `Ones`,
`Fill`, `Trues` and `Falses`, and imports those names from FillArrays. A call is repaired only when no code
in its function writes the array; with `unsafe`, an array that leaves the function is repaired too.
"""
constant_array_plan(repository::Repository, directories::Tuple{Vararg{String}}, unsafe::Bool)::FixPlan{FillRewrite, typeof(filled_texts)} =
    FixPlan(collect(Repair{FillRewrite}, Iterators.flatten(constant_array_repairs.(directory_sources(repository, directories), unsafe))), filled_texts)

# Import placement over a module: a root file and every file it includes by literal path. An import item
# belongs in the files that use its name: one no file uses goes, one only other files use moves to them.

const USING_KIND = SYNTAX.@K_str "using"
const IMPORT_KIND = SYNTAX.@K_str "import"
const COLON_KIND = SYNTAX.@K_str ":"
const AS_KIND = SYNTAX.@K_str "as"
const CALL_KIND = SYNTAX.@K_str "call"
const STRING_KIND = SYNTAX.@K_str "string"
const STRING_TEXT_KIND = SYNTAX.@K_str "String"
const MACRO_NAME_KIND = SYNTAX.@K_str "macro_name"
const MODULE_KIND = SYNTAX.@K_str "module"
const STRING_MACRO_NAME_KIND = SYNTAX.@K_str "StrMacroName"
const COMMAND_TEXT_KIND = SYNTAX.@K_str "CmdString"
# An import opts out on its own line or the line above; Fatou's own opt-out counts.
const IMPORT_OPT_OUT = r"fatou-ignore\s+unused-import|lint:\s*misplaced-import"
# A name the rule places: an identifier or macro. Operators (`import Base: +`) are used without a name token.
const PLACED_NAME = r"^@?[\p{L}_]"

"""One name an import binds: `name` as code spells it (`@test`, `s` for `r as s`) and the `text` declaring it."""
struct ImportItem
    name::String
    text::String
end

"""
An import statement: `prefix` (`using M: ` or `import `) before its `items`, at bytes
`first_byte:last_byte`, starting on `line`. A `pinned` one (a bare `using M`, or opted out) stays.
A `nested` one sits in a `module` block of its file and serves only that block and its includes.
"""
struct ImportStatement
    prefix::String
    items::Vector{ImportItem}
    first_byte::Int
    last_byte::Int
    line::Int
    pinned::Bool
    nested::Bool
end

"""
A parsed Julia file: the names it uses outside imports, its import statements, and the paths it
includes (`""` for an include no literal names). An `editable` file is one the rule checks.
"""
struct ImportFile
    path::String
    text::String
    used::Set{String}
    statements::Vector{ImportStatement}
    includes::Vector{String}
    editable::Bool
end

"""An import `item` of `statement` that `file` does not use: it goes from `file` and is added to each of `targets` (none when no other file needs it)."""
struct ImportMove
    file::String
    statement::ImportStatement
    item::ImportItem
    targets::Vector{String}
end

"""The names used by the interpolations in command text `text`, found by Julia's own `Base.shell_parse` (none inside single quotes)."""
function interpolated_names(text::AbstractString)::Vector{String}
    return expression_names(first(Base.shell_parse(text)))
end

"""The names a parsed expression uses; a `QuoteNode` (a field name) uses none."""
expression_names(name::Symbol)::Vector{String} = [String(name)]
expression_names(expression::Expr)::Vector{String} = String[name for argument in expression.args for name in expression_names(argument)]
expression_names(::Any)::Vector{String} = String[]

"""The names syntax `node` uses: identifiers, macros and string macros, without field names and import statements."""
function name_tokens(node::SYNTAX.SyntaxNode)::Vector{String}
    kind = SYNTAX.kind(node)
    if kind === USING_KIND || kind === IMPORT_KIND
        return String[]
    elseif kind === IDENTIFIER_KIND
        return [String(SYNTAX.sourcetext(node))]
    elseif kind === STRING_MACRO_NAME_KIND
        return ["@" * SYNTAX.sourcetext(node) * "_str"]
    elseif kind === COMMAND_TEXT_KIND
        return interpolated_names(SYNTAX.sourcetext(node))
    elseif SYNTAX.is_leaf(node)
        return String[]
    elseif kind === MACRO_NAME_KIND
        return ["@" * SYNTAX.sourcetext(only(SYNTAX.children(node)))]
    end
    children = SYNTAX.children(node)
    if kind === FIELD_KIND
        return name_tokens(first(children))
    end
    return String[name for child in children for name in name_tokens(child)]
end

"""Every `using` and `import` statement below `node`, outside quotes."""
function import_nodes(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    kind = SYNTAX.kind(node)
    if kind === USING_KIND || kind === IMPORT_KIND
        return [node]
    elseif SYNTAX.is_leaf(node) || kind === QUOTE_KIND
        return SYNTAX.SyntaxNode[]
    end
    return SYNTAX.SyntaxNode[found for child in SYNTAX.children(node) for found in import_nodes(child)]
end

"""Every `module` block below `node`."""
function module_nodes(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    if SYNTAX.is_leaf(node)
        return SYNTAX.SyntaxNode[]
    end
    below = SYNTAX.SyntaxNode[found for child in SYNTAX.children(node) for found in module_nodes(child)]
    if SYNTAX.kind(node) === MODULE_KIND
        return vcat([node], below)
    end
    return below
end

"""The name parsed import item `node` binds."""
function item_name(node::SYNTAX.SyntaxNode)::String
    if SYNTAX.kind(node) === AS_KIND
        return String(SYNTAX.sourcetext(last(SYNTAX.children(node))))
    end
    tail = last(SYNTAX.children(node))
    if SYNTAX.kind(tail) === MACRO_NAME_KIND
        return "@" * SYNTAX.sourcetext(only(SYNTAX.children(tail)))
    end
    return String(SYNTAX.sourcetext(tail))
end

"""The statement a `using` or `import` `node` of `text` (split into `lines`) declares; `nested` when it sits in a `module` block."""
function import_statement(node::SYNTAX.SyntaxNode, text::AbstractString, lines::AbstractVector{<:AbstractString}, nested::Bool)::ImportStatement
    keyword = "import"
    if SYNTAX.kind(node) === USING_KIND
        keyword = "using"
    end
    children = SYNTAX.children(node)
    colon = length(children) == 1 && SYNTAX.kind(only(children)) === COLON_KIND
    prefix = keyword * " "
    item_nodes = children
    if colon
        parts = SYNTAX.children(only(children))
        prefix = keyword * " " * strip(text[SYNTAX.byte_range(first(parts))]) * ": "
        item_nodes = parts[2:end]
    end
    items::Vector{ImportItem} = [ImportItem(item_name(item), strip(text[SYNTAX.byte_range(item)])) for item in item_nodes]
    line = first(SYNTAX.source_location(node))
    opted_out = occursin(IMPORT_OPT_OUT, join(lines[max(1, line - 1):line], "\n"))
    bytes = SYNTAX.byte_range(node)
    return ImportStatement(prefix, items, first(bytes), last(bytes), line, opted_out || (keyword == "using" && !colon), nested)
end

"""Whether `node` is a string literal with no interpolation."""
is_literal_string(node::SYNTAX.SyntaxNode)::Bool =
    SYNTAX.kind(node) === STRING_KIND && length(SYNTAX.children(node)) == 1 && SYNTAX.kind(only(SYNTAX.children(node))) === STRING_TEXT_KIND

"""The path pieces of include argument `node`: `"a.jl"` or `joinpath(@__DIR__, "a", "b.jl")`; empty for anything else."""
function literal_pieces(node::SYNTAX.SyntaxNode)::Vector{String}
    if is_literal_string(node)
        return [String(SYNTAX.sourcetext(only(SYNTAX.children(node))))]
    elseif SYNTAX.kind(node) !== CALL_KIND
        return String[]
    end
    parts = SYNTAX.children(node)
    if length(parts) >= 3 && SYNTAX.sourcetext(first(parts)) == "joinpath" && SYNTAX.sourcetext(parts[2]) == "@__DIR__" && all(is_literal_string, parts[3:end])
        return [String(SYNTAX.sourcetext(only(SYNTAX.children(part)))) for part in parts[3:end]]
    end
    return String[]
end

"""The paths the `include` calls below `node` name, relative to `directory`; `""` for one whose path is not a literal."""
function include_paths(node::SYNTAX.SyntaxNode, directory::AbstractString)::Vector{String}
    kind = SYNTAX.kind(node)
    if SYNTAX.is_leaf(node) || kind === QUOTE_KIND
        return String[]
    end
    children = SYNTAX.children(node)
    if kind === CALL_KIND && SYNTAX.kind(first(children)) === IDENTIFIER_KIND && SYNTAX.sourcetext(first(children)) == "include"
        pieces = String[]
        if length(children) == 2
            pieces = literal_pieces(last(children))
        end
        if isempty(pieces)
            return [""]
        end
        return [normpath(joinpath(directory, pieces...))]
    end
    return String[path for child in children for path in include_paths(child, directory)]
end

"""Julia file `path` parsed for import placement; `editable` marks a file the rule checks and rewrites."""
function import_file(path::AbstractString, editable::Bool)::ImportFile
    text = read(path, String)
    tree = SYNTAX.parseall(SYNTAX.SyntaxNode, text; filename = path)
    lines = split(text, '\n')
    modules = [SYNTAX.byte_range(node) for node in module_nodes(tree)]
    nodes = import_nodes(tree)
    statements = ImportStatement[import_statement.(nodes, text, (lines,), inside_module.(nodes, (modules,)))...]
    return ImportFile(normpath(path), text, Set(name_tokens(tree)), statements, include_paths(tree, dirname(path)), editable)
end

"""Whether `node` starts inside one of the byte ranges `modules`."""
inside_module(node::SYNTAX.SyntaxNode, modules::AbstractVector{<:UnitRange})::Bool = any(in.(first(SYNTAX.byte_range(node)), modules))

"""Whether `statement` imports `name`."""
statement_imports(statement::ImportStatement, name::AbstractString)::Bool = any(==(name), [item.name for item in statement.items])

"""Whether `file` imports `name`."""
imports_name(file::ImportFile, name::AbstractString)::Bool = any(Base.Fix2(statement_imports, name), file.statements)

"""
The files of the module rooted at `path`: it and every file it includes, transitively. An include
outside `known` is parsed as a file the rule reads but never rewrites; an unreadable one is a blank mark.
"""
function unit_files(path::AbstractString, known::AbstractDict{String, ImportFile}, seen::AbstractVector{String})::Vector{ImportFile}
    if path in seen
        return ImportFile[]
    elseif path == "" || !isfile(path)
        return [ImportFile("", "", Set{String}(), ImportStatement[], String[], false)]
    end
    file::ImportFile = if haskey(known, path)
        known[path]
    else
        import_file(path, false)
    end
    below::Vector{String} = vcat(seen, [path])
    return reduce(vcat, unit_files.(file.includes, (known,), (below,)); init = [file])
end

"""Whether `file` has a bare `using M`, which may bring in any name `M` exports."""
has_bare_using(file::ImportFile)::Bool = any(statement.prefix == "using " for statement in file.statements)

"""
The moves in one module's `unit`; none when it holds an include the rule cannot follow. A bare
`using M` anywhere in the unit may supply any name, so a file that uses a name without importing it
is no target then. Files outside the checked directories (a vendored package's tests) bring their
own imports, so they count as no user.
"""
function unit_moves(unit::AbstractVector{ImportFile})::Vector{ImportMove}
    if any(file -> file.path == "", unit)
        return ImportMove[]
    end
    supplied = any(has_bare_using, unit)
    editable = filter(file -> file.editable, unit)
    return reduce(vcat, file_moves.((unit,), supplied, editable); init = ImportMove[])
end

"""The moves of the unpinned statements of `file`, one of `unit`; `supplied` when a bare `using` is in the unit."""
file_moves(unit::AbstractVector{ImportFile}, supplied::Bool, file::ImportFile)::Vector{ImportMove} = reduce(
    vcat, statement_moves.((unit,), supplied, (file,), filter(statement -> !statement.pinned, file.statements)); init = ImportMove[],
)

"""The moves of the items of `statement` in `file` that `file` does not use."""
function statement_moves(unit::AbstractVector{ImportFile}, supplied::Bool, file::ImportFile, statement::ImportStatement)::Vector{ImportMove}
    items = filter(Base.Fix1(placeable, file), statement.items)
    return ImportMove.(file.path, (statement,), items, move_targets.((unit,), supplied, (file,), (statement,), items))
end

"""Whether `item` is a name the rule places and `file` does not use."""
placeable(file::ImportFile, item::ImportItem)::Bool = occursin(PLACED_NAME, item.name) && !(item.name in file.used)

"""The files of `unit` that use `item` of `statement` in `file` without importing it, where the item can move."""
function move_targets(unit::AbstractVector{ImportFile}, supplied::Bool, file::ImportFile, statement::ImportStatement, item::ImportItem)::Vector{String}
    targets = unit[move_target.(unit, supplied, (file,), (statement,), (item,))]
    return unique([target.path for target in targets])
end

"""Whether `item` of `statement` in `file` can move to `other`: it uses the name, does not import it, and a nested statement only moves into an include."""
move_target(other::ImportFile, supplied::Bool, file::ImportFile, statement::ImportStatement, item::ImportItem)::Bool =
    other.editable && !supplied && other.path != file.path && item.name in other.used &&
    !imports_name(other, item.name) && (!statement.nested || other.path in file.includes)

"""Every import move in `files` (the rule's own), module by module; a file in two modules is left alone."""
function import_moves(files::AbstractVector{ImportFile})::Vector{ImportMove} # lint: abstract-local  files have different numbers of units
    known::Dict{String, ImportFile} = Dict(file.path => file for file in files)
    included::Set{String} = Set(path for file in files for path in file.includes)
    roots = filter(!Base.Fix2(in, included), [file.path for file in files])
    units = unit_files.(roots, (known,), (String[],))
    paths = collect(keys(known))
    membership::Dict{String, Int} = Dict(paths .=> unit_count.((units,), paths))
    return filter(Base.Fix1(single_unit, membership), reduce(vcat, unit_moves.(units); init = ImportMove[]))
end

"""How many of `units` (each a module's files, ragged) hold the file at `path`."""
unit_count(units::AbstractVector, path::String)::Int = count(Base.Fix2(unit_holds, path), units)

"""Whether `unit` holds the file at `path`."""
unit_holds(unit::AbstractVector{ImportFile}, path::String)::Bool = path in [file.path for file in unit]

"""Whether `move`'s file and targets each sit in one unit of `membership`."""
single_unit(membership::AbstractDict{String, Int}, move::ImportMove)::Bool =
    membership[move.file] == 1 && all(==(1), get.((membership,), move.targets, 0))

"""One site per move, keyed by file and name, at the import's line."""
import_sites(moves::AbstractVector{ImportMove})::Vector{Site} = [Site("$(basename(move.file)) $(move.item.name)", move.file, move.statement.line, "") for move in moves]

"""The Julia files of `directories` in `repository`, parsed for import placement."""
import_files(repository::Repository, directories::Tuple{Vararg{String}})::Vector{ImportFile} =
    [import_file(path, true) for path in repository_sources(repository, directories)]

"""
    misplaced_imports(repository, directories)

One site per import item in `directories` that its file does not use: one that no file of its module
uses, or that other files of the module use. `place_imports!` fixes them.
"""
misplaced_imports(repository::Repository, directories::Tuple{Vararg{String}})::Vector{Site} = import_sites(import_moves(import_files(repository, directories)))

"""The first byte of the line holding byte `index` of `bytes`."""
line_start(bytes::AbstractVector{UInt8}, index::Integer)::Int = something(findprev(==(UInt8('\n')), bytes, index - 1), 0) + 1

"""The last byte (the newline) of the line holding byte `index` of `bytes`."""
line_end(bytes::AbstractVector{UInt8}, index::Integer)::Int = something(findnext(==(UInt8('\n')), bytes, index), length(bytes))

"""Whether `byte` is a space or tab."""
is_blank(byte::Unsigned)::Bool = byte == UInt8(' ') || byte == UInt8('\t')

"""The edit taking `removed` items out of `statement` in `bytes`: the statement rewritten, or its whole lines deleted when nothing stays."""
function removal_edit(bytes::AbstractVector{UInt8}, statement::ImportStatement, removed::AbstractVector{ImportItem})::Pair{UnitRange{Int}, String}
    kept::Vector{String} = [item.text for item in filter(!Base.Fix2(in, removed), statement.items)]
    if !isempty(kept)
        return (statement.first_byte:statement.last_byte) => statement.prefix * join(kept, ", ")
    end
    start = line_start(bytes, statement.first_byte)
    if all(is_blank, view(bytes, start:(statement.first_byte - 1)))
        return (start:line_end(bytes, statement.last_byte)) => ""
    end
    return (statement.first_byte:statement.last_byte) => ""
end

"""The import statement of the `items` (prefix => item text) under `prefix`."""
prefix_statement(items::AbstractVector{Pair{String, String}}, prefix::String)::String =
    prefix * join(unique([text for (owner, text) in items if owner == prefix]), ", ")

"""The edit adding `items` (prefix => item text) to `file`: after its last import, at that import's indent, or at the top of a file with none."""
function addition_edit(file::ImportFile, items::AbstractVector{Pair{String, String}})::Pair{UnitRange{Int}, String}
    statements::Vector{String} = prefix_statement.((items,), unique(first.(items)))
    if isempty(file.statements)
        if occursin(r"^\s*(bare)?module\s"m, file.text)
            error("$(file.path) holds a module but no import to place $(statements) beside")
        end
        return (1:0) => join(statements .* "\n")
    end
    bytes = codeunits(file.text)
    last_statement = argmax(statement -> statement.last_byte, file.statements)
    start = line_start(bytes, last_statement.first_byte)
    indent = String(bytes[start:(start + findfirst(!is_blank, view(bytes, start:length(bytes))) - 2)])
    stop = line_end(bytes, last_statement.last_byte)
    return ((stop + 1):stop) => join(indent .* statements .* "\n")
end

"""The text of `file` after `moves`: its moved items taken out, and the items moved to it added."""
function placed_text(file::ImportFile, moves::AbstractVector{ImportMove})::String
    bytes = codeunits(file.text)
    own::Vector{ImportMove} = moves[[move.file for move in moves] .== file.path]
    touched = filter(!isempty ∘ Base.Fix1(moved_items, own), file.statements)
    removals::Vector{Pair{UnitRange{Int}, String}} = removal_edit.((bytes,), touched, moved_items.((own,), touched))
    incoming = moves[in.(file.path, [move.targets for move in moves])]
    added::Vector{Pair{String, String}} = [move.statement.prefix => move.item.text for move in incoming]
    additions = Pair{UnitRange{Int}, String}[]
    if !isempty(added)
        additions = [addition_edit(file, added)]
    end
    edits::Vector{Pair{UnitRange{Int}, String}} = sort(vcat(removals, additions); by = edit -> first(first(edit)), rev = true)
    text::String = file.text
    for (range, replacement) in edits
        text = splice_text(text, range, replacement)
    end
    return text
end

"""The items `moves` take out of `statement`."""
moved_items(moves::AbstractVector{ImportMove}, statement::ImportStatement)::Vector{ImportItem} =
    [move.item for move in moves[[move.statement for move in moves] .=== (statement,)]]

"""The text `text` with the bytes of `range` replaced by `replacement`."""
function splice_text(text::T, range::UnitRange{Int}, replacement::AbstractString)::String where {T <: AbstractString}
    source = codeunits(text)
    return String(vcat(source[1:(first(range) - 1)], codeunits(replacement), source[(last(range) + 1):end]))
end

"""
    place_imports!(repository, directories)

Rewrite the Julia files of `directories` so every import sits in the files that use it: each
`misplaced_imports` site is deleted, or moved into the module's files that use it. Returns the sites.
"""
function place_imports!(repository::Repository, directories::Tuple{Vararg{String}})::Vector{Site}
    files = import_files(repository, directories)
    moves = import_moves(files)
    touched = Set(reduce(vcat, [vcat([move.file], move.targets) for move in moves]; init = String[]))
    rewritten = files[in.([file.path for file in files], (touched,))]
    write.([file.path for file in rewritten], placed_text.(rewritten, (moves,)))
    return import_sites(moves)
end

# Import placement over a module: a root file and every file it includes by literal path. An import item
# belongs in the files that use its name: one no file uses goes, one only other files use moves to them.

const USING_KIND = SYNTAX.@K_str "using"
const IMPORT_KIND = SYNTAX.@K_str "import"
const COLON_KIND = SYNTAX.@K_str ":"
const AS_KIND = SYNTAX.@K_str "as"
const CALL_KIND = SYNTAX.@K_str "call"
const DOC_KIND = SYNTAX.@K_str "doc"
const MACRO_NAME_KIND = SYNTAX.@K_str "macro_name"
const MODULE_KIND = SYNTAX.@K_str "module"
const STRING_MACRO_NAME_KIND = SYNTAX.@K_str "StrMacroName"
const COMMAND_TEXT_KIND = SYNTAX.@K_str "CmdString"
# Fatou's own opt-out, on an import's line or the line above, also pins it.
const FATOU_OPT_OUT = r"fatou-ignore\s+unused-import"
# What goes with a statement cut out of its line: the blanks after it, and a `;` with the blanks after that.
const STATEMENT_TAIL = r"^[ \t]*(;[ \t]*)?"
# A name the rule places: an identifier or macro. Operators (`import Base: +`) are used without a name token.
const PLACED_NAME = r"^@?[\p{L}_]"

"""One name an import binds: `name` as code spells it (`@test`, `s` for `r as s`) and the `text` declaring it."""
struct ImportItem
    name::String
    text::String
end

"""
An import statement: `prefix` (`using M: ` or `import `) before its `items`, at bytes
`first_byte:last_byte`, on lines `line:last_line`. A `pinned` one (a bare `using M`, or one Fatou's
`unused-import` opt-out names) stays. `block` is the first byte of the innermost `module` block of its file that holds it,
0 at the file's top level: a nested statement serves only that block and the files it includes.
"""
struct ImportStatement
    prefix::String
    items::Vector{ImportItem}
    first_byte::Int
    last_byte::Int
    line::Int
    last_line::Int
    pinned::Bool
    block::Int
end

"""
A parsed Julia file: the names it uses outside imports, the names its relative imports take from
other modules of the package (`relayed_names`), its import statements, and the paths it includes
(`""` for an include no literal names), each with the `module` block it sits in (`include_blocks`, as
`ImportStatement`'s `block`). An `editable` file is one the rule checks. A file that `opens_module`
holds only `module` blocks at its top level, so its names are another module's.
"""
struct ImportFile
    path::String
    text::String
    used::Set{String}
    relayed::Set{String}
    statements::Vector{ImportStatement}
    includes::Vector{String}
    include_blocks::Vector{Int}
    editable::Bool
    opens_module::Bool
end

"""
One file of a module's unit, with its `scope`: the chain of `module` blocks, each named by file and
first byte, that the unit's root reaches it through. A file included inside a block is that block's module's.
"""
struct UnitFile
    file::ImportFile
    scope::String
end

"""The scope of code in `block` (0 for the top level) of the file `unit` holds."""
function block_scope(unit::UnitFile, block::Integer)::String
    if block == 0
        return unit.scope
    end
    return "$(unit.scope)|$(unit.file.path)@$block"
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
    return path_name(node)
end

"""The last part of parsed import path `node` (`f` of `..Parent.f`, `@m` of `A.@m`)."""
function path_name(node::SYNTAX.SyntaxNode)::String
    tail = last(SYNTAX.children(node))
    if SYNTAX.kind(tail) === MACRO_NAME_KIND
        return "@" * SYNTAX.sourcetext(only(SYNTAX.children(tail)))
    end
    return String(SYNTAX.sourcetext(tail))
end

"""The import path of parsed import item `node`: the path before `as`, or `node` itself."""
function item_path(node::SYNTAX.SyntaxNode)::SYNTAX.SyntaxNode
    if SYNTAX.kind(node) === AS_KIND
        return first(SYNTAX.children(node))
    end
    return node
end

"""Whether parsed import path `node` starts with a `.`, naming a module relative to its own (`..Parent`, `.Sub`)."""
relative_path(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(first(SYNTAX.children(node))) === FIELD_KIND

"""
The names `using` or `import` `node` takes from a module of its own package by a relative path:
`f` of `using ..Parent: f as g` or of `import .Sub.f`. The module that supplies each needs its own import of it.
"""
function relayed_names(node::SYNTAX.SyntaxNode)::Vector{String}
    children = SYNTAX.children(node)
    if length(children) == 1 && SYNTAX.kind(only(children)) === COLON_KIND
        parts = SYNTAX.children(only(children))
        if relative_path(first(parts))
            return path_name.(item_path.(parts[2:end]))
        end
        return String[]
    end
    return path_name.(filter(relative_path, item_path.(children)))
end

"""
The statement a `using` or `import` `node` of `text` (split into `lines`) declares, in the `module`
block starting at byte `block` (0 at the top level).
"""
function import_statement(node::SYNTAX.SyntaxNode, text::AbstractString, lines::AbstractVector{<:AbstractString}, block::Integer)::ImportStatement
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
    bytes = SYNTAX.byte_range(node)
    last_line = line + count(==('\n'), text[bytes])
    opted_out = occursin(FATOU_OPT_OUT, join(lines[max(1, line - 1):line], "\n"))
    return ImportStatement(prefix, items, first(bytes), last(bytes), line, last_line, opted_out || (keyword == "using" && !colon), block)
end

"""Every `include` call below `node`, outside quotes."""
function include_nodes(node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    kind = SYNTAX.kind(node)
    if SYNTAX.is_leaf(node) || kind === QUOTE_KIND
        return SYNTAX.SyntaxNode[]
    end
    children = SYNTAX.children(node)
    if kind === CALL_KIND && SYNTAX.kind(first(children)) === IDENTIFIER_KIND && SYNTAX.sourcetext(first(children)) == "include"
        return [node]
    end
    return SYNTAX.SyntaxNode[found for child in children for found in include_nodes(child)]
end

"""
The path `include` call `node` names, relative to `directory` and resolved by `included_path`; `""`
for one whose path is not a literal.
"""
function include_path(node::SYNTAX.SyntaxNode, directory::AbstractString)::String
    children = SYNTAX.children(node)
    if length(children) != 2
        return ""
    end
    return something(included_path(Expr(last(children)), directory), "")
end

"""The first byte of the innermost of the `module` block byte ranges `modules` that holds `node`; 0 for none."""
module_block(node::SYNTAX.SyntaxNode, modules::AbstractVector{<:UnitRange})::Int =
    maximum(first.(modules[in.(first(SYNTAX.byte_range(node)), modules)]); init = 0)

"""The kind of top-level `statement`, or of the statement its docstring documents."""
function documented_kind(statement::SYNTAX.SyntaxNode)::SYNTAX.Kind
    if SYNTAX.kind(statement) === DOC_KIND
        return SYNTAX.kind(last(SYNTAX.children(statement)))
    end
    return SYNTAX.kind(statement)
end

"""Whether parsed file `tree` holds only `module` blocks, documented or not, at its top level."""
function opens_module(tree::SYNTAX.SyntaxNode)::Bool
    kinds::Vector{SYNTAX.Kind} = [documented_kind(statement) for statement in SYNTAX.children(tree)]
    return !isempty(kinds) && all(==(MODULE_KIND), kinds)
end

"""
The parsed Julia file `source` read for import placement; `editable` marks a file the rule checks and
rewrites.
"""
function import_file(source::Source, editable::Bool)::ImportFile
    (; path, text, tree) = source
    lines = split(text, '\n')
    modules = [SYNTAX.byte_range(node) for node in module_nodes(tree)]
    nodes = import_nodes(tree)
    statements = ImportStatement[import_statement.(nodes, text, (lines,), module_block.(nodes, (modules,)))...]
    includes = include_nodes(tree)
    return ImportFile(
        normpath(path), text, Set(name_tokens(tree)), Set{String}(reduce(vcat, relayed_names.(nodes); init = String[])),
        statements, include_path.(includes, dirname(path)),
        module_block.(includes, (modules,)), editable, opens_module(tree),
    )
end

"""Whether `statement` imports `name`."""
statement_imports(statement::ImportStatement, name::AbstractString)::Bool = any(==(name), [item.name for item in statement.items])

"""Whether `file` imports `name`."""
imports_name(file::ImportFile, name::AbstractString)::Bool = any(Base.Fix2(statement_imports, name), file.statements)

"""
The files of the module rooted at `path`, reached in `scope`: it and every file it includes,
transitively, each in the scope of the block its include sits in (`block_scope`). An include outside
`known` is parsed as a file the rule reads but never rewrites; an unreadable one is a blank mark.
"""
function unit_files(path::AbstractString, known::AbstractDict{String, ImportFile}, seen::AbstractVector{String}, scope::String)::Vector{UnitFile}
    if path in seen
        return UnitFile[]
    elseif !haskey(known, path) && (path == "" || !isfile(path))
        return [UnitFile(ImportFile("", "", Set{String}(), Set{String}(), ImportStatement[], String[], Int[], false, false), scope)]
    end
    file::ImportFile = if haskey(known, path)
        known[path]
    else
        import_file(Source(Repository(dirname(path)), path), false)
    end
    unit = UnitFile(file, scope)
    below::Vector{String} = vcat(seen, [path])
    return reduce(vcat, unit_files.(file.includes, (known,), (below,), block_scope.((unit,), file.include_blocks)); init = [unit])
end

"""Whether `file` has a bare `using M`, which may bring in any name `M` exports."""
has_bare_using(file::ImportFile)::Bool = any(statement.prefix == "using " for statement in file.statements)

"""Whether `unit` holds a file in two scopes: one included both inside and outside a `module` block."""
split_scope(unit::AbstractVector{UnitFile})::Bool = length(unique([(entry.file.path, entry.scope) for entry in unit])) > length(unique([entry.file.path for entry in unit]))

"""
The moves in one module's `unit`; none when it holds an include the rule cannot follow, or a file in
two scopes. A bare `using M` anywhere in the unit may supply any name, so a file that uses a name
without importing it is no target then. Files outside the checked directories (a vendored package's
tests) bring their own imports, so they count as no user. A name a relative import in the unit takes
from another of its modules (`using ..Parent: f`) stays wherever the unit imports it.
"""
function unit_moves(unit::AbstractVector{UnitFile})::Vector{ImportMove}
    if any(entry -> entry.file.path == "", unit) || split_scope(unit)
        return ImportMove[]
    end
    supplied = any(has_bare_using, getfield.(unit, :file))
    relayed = Set{String}(name for entry in unit for name in entry.file.relayed)
    editable = filter(entry -> entry.file.editable, unit)
    return reduce(vcat, file_moves.((unit,), supplied, (relayed,), editable); init = ImportMove[])
end

"""The moves of the unpinned statements of `entry`, one of `unit`; `supplied` when a bare `using` is in the unit, `relayed` the unit's `relayed_names`."""
file_moves(unit::AbstractVector{UnitFile}, supplied::Bool, relayed::AbstractSet{String}, entry::UnitFile)::Vector{ImportMove} = reduce(
    vcat, statement_moves.((unit,), supplied, (relayed,), (entry,), filter(statement -> !statement.pinned, entry.file.statements)); init = ImportMove[],
)

"""The moves of the items of `statement` in `entry` that its file does not use and no relative import in the unit takes (`relayed`)."""
function statement_moves(
        unit::AbstractVector{UnitFile}, supplied::Bool, relayed::AbstractSet{String}, entry::UnitFile, statement::ImportStatement,
    )::Vector{ImportMove}
    items = filter(!Base.Fix1(names_item, relayed), filter(Base.Fix1(placeable, entry.file), statement.items))
    return ImportMove.(entry.file.path, (statement,), items, move_targets.((unit,), supplied, (entry,), (statement,), items))
end

"""Whether `names` holds the name `item` binds."""
names_item(names::AbstractSet{String}, item::ImportItem)::Bool = item.name in names

"""Whether `item` is a name the rule places and `file` does not use."""
placeable(file::ImportFile, item::ImportItem)::Bool = occursin(PLACED_NAME, item.name) && !(item.name in file.used)

"""The files of `unit` that use `item` of `statement` in `entry` without importing it, where the item can move."""
function move_targets(unit::AbstractVector{UnitFile}, supplied::Bool, entry::UnitFile, statement::ImportStatement, item::ImportItem)::Vector{String}
    targets = unit[move_target.(unit, supplied, (entry,), (statement,), (item,))]
    return unique([target.file.path for target in targets])
end

"""
Whether `item` of `statement` in `entry` can move to `other`: its file uses the name, does not import
it, does not open a module of its own, and sits in the statement's scope (`block_scope`), so a file
included inside a `module` block takes only that block's imports.
"""
function move_target(other::UnitFile, supplied::Bool, entry::UnitFile, statement::ImportStatement, item::ImportItem)::Bool
    target = other.file
    return target.editable && !target.opens_module && !supplied && target.path != entry.file.path && item.name in target.used &&
        !imports_name(target, item.name) && other.scope == block_scope(entry, statement.block)
end

"""Every import move in `files` (the rule's own), module by module; a file in two modules is left alone."""
function import_moves(files::AbstractVector{ImportFile})::Vector{ImportMove} # lint: abstract-local  files have different numbers of units
    known::Dict{String, ImportFile} = Dict(file.path => file for file in files)
    included::Set{String} = Set(path for file in files for path in file.includes)
    roots = filter(!Base.Fix2(in, included), [file.path for file in files])
    units = unit_files.(roots, (known,), (String[],), "")
    paths = collect(keys(known))
    membership::Dict{String, Int} = Dict(paths .=> unit_count.((units,), paths))
    return filter(Base.Fix1(single_unit, membership), reduce(vcat, unit_moves.(units); init = ImportMove[]))
end

"""How many of `units` (each a module's files, ragged) hold the file at `path`."""
unit_count(units::AbstractVector, path::String)::Int = count(Base.Fix2(unit_holds, path), units)

"""Whether `unit` holds the file at `path`."""
unit_holds(unit::AbstractVector{UnitFile}, path::String)::Bool = path in [entry.file.path for entry in unit]

"""Whether `move`'s file and targets each sit in one unit of `membership`."""
single_unit(membership::AbstractDict{String, Int}, move::ImportMove)::Bool =
    membership[move.file] == 1 && all(==(1), get.((membership,), move.targets, 0))

"""One site per move, keyed by file and name, at the import's lines."""
import_sites(repository::Repository, moves::AbstractVector{ImportMove})::Vector{Site} = map(Base.Fix1(import_site, repository), moves)

"""The site of `move` in `repository`, keyed by file and name, at the import's lines."""
import_site(repository::Repository, move::ImportMove)::Site =
    Site("$(file_key(repository, move.file)) $(move.item.name)", move.file, move.statement.line, move.statement.last_line, "")

"""The parsed Julia files of `directories` in `repository`."""
directory_sources(repository::Repository, directories::Tuple{Vararg{String}})::Vector{Source} =
    Source.((repository,), repository_sources(repository, directories))

"""
    misplaced_imports(repository, directories)
    misplaced_imports(repository, sources)

One site per import item in `directories` (or the parsed files `sources`) that its file does not use:
one that no file of its module uses, or that other files of the module use. `import_plan` fixes them.
"""
misplaced_imports(repository::Repository, directories::Tuple{Vararg{String}})::Vector{Site} =
    misplaced_imports(repository, directory_sources(repository, directories))

misplaced_imports(repository::Repository, sources::AbstractVector{Source})::Vector{Site} =
    import_sites(repository, import_moves(import_file.(sources, true)))

"""The first byte of the line holding byte `index` of `bytes`."""
line_start(bytes::AbstractVector{UInt8}, index::Integer)::Int = something(findprev(==(UInt8('\n')), bytes, index - 1), 0) + 1

"""The last byte (the newline) of the line holding byte `index` of `bytes`."""
line_end(bytes::AbstractVector{UInt8}, index::Integer)::Int = something(findnext(==(UInt8('\n')), bytes, index), length(bytes))

"""Whether `byte` is a space or tab."""
is_blank(byte::Unsigned)::Bool = byte == UInt8(' ') || byte == UInt8('\t')

"""
The edit taking `removed` items out of `statement` in `bytes`: the statement rewritten, or deleted when
nothing stays. A deleted statement takes its `STATEMENT_TAIL`, and its whole lines when only blanks
come before it and only a comment after.
"""
function removal_edit(bytes::AbstractVector{UInt8}, statement::ImportStatement, removed::AbstractVector{ImportItem})::Pair{UnitRange{Int}, String}
    kept::Vector{String} = [item.text for item in filter(!Base.Fix2(in, removed), statement.items)]
    if !isempty(kept)
        return (statement.first_byte:statement.last_byte) => statement.prefix * join(kept, ", ")
    end
    start = line_start(bytes, statement.first_byte)
    stop = line_end(bytes, statement.last_byte)
    after = String(bytes[(statement.last_byte + 1):stop])
    tail = ncodeunits(match(STATEMENT_TAIL, after).match)
    rest = strip(after[(tail + 1):end])
    if all(is_blank, view(bytes, start:(statement.first_byte - 1))) && (isempty(rest) || startswith(rest, '#'))
        return (start:stop) => ""
    end
    return (statement.first_byte:(statement.last_byte + tail)) => ""
end

"""The import statement of the `items` (prefix => item text) under `prefix`."""
prefix_statement(items::AbstractVector{Pair{String, String}}, prefix::String)::String =
    prefix * join(unique([text for (owner, text) in items if owner == prefix]), ", ")

"""Whether `statement` sits at the top level of its file, outside every `module` block."""
top_level(statement::ImportStatement)::Bool = statement.block == 0

"""The last byte of `statement`."""
last_byte(statement::ImportStatement)::Int = statement.last_byte

"""
The edit adding `items` (prefix => item text) to `file`: after its last top-level import, at that
import's indent, or at the top of a file with none.
"""
function addition_edit(file::ImportFile, items::AbstractVector{Pair{String, String}})::Pair{UnitRange{Int}, String}
    statements::Vector{String} = prefix_statement.((items,), unique(first.(items)))
    top = filter(top_level, file.statements)
    if isempty(top)
        return (1:0) => join(statements .* "\n")
    end
    bytes = codeunits(file.text)
    last_statement = argmax(last_byte, top)
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

"""The new text of `files` (`placed_text`) after import moves, as path => text for each file the moves touch."""
struct PlacedTexts
    files::Vector{ImportFile}
end

function (placed::PlacedTexts)(moves::AbstractVector{ImportMove})::Vector{Pair{String, String}}
    touched = Set(reduce(vcat, [vcat([move.file], move.targets) for move in moves]; init = String[]))
    return [file.path => placed_text(file, moves) for file in placed.files if file.path in touched]
end

"""
    import_plan(repository, directories)

The `FixPlan` that puts every import of `directories` in the files that use it: one repair per
`misplaced_imports` site, which deletes the item, or moves it into the module's files that use it.
"""
function import_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ImportMove, PlacedTexts}
    files = import_file.(directory_sources(repository, directories), true)
    moves = import_moves(files)
    return FixPlan(Repair{ImportMove}[Repair(import_site(repository, move), move) for move in moves], PlacedTexts(files))
end

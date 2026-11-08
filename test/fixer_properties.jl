# Properties every registered fixer keeps on small generated packages: imports, nested modules,
# includes, `where` clauses, concatenating folds, opt-out comments and code sharing a line with an import.

using Test: @testset, @test
using Supposition: Supposition, Data, @check
using Corset: Corset
using TOML: TOML

const SYNTAX = Corset.SYNTAX

# The rules whose fixers the generator below exercises.
const GENERATED_FIXERS = Set(["misplaced-import", "quadratic-vcat", "where-return"])

# The rules whose fixers only the example tests in runtests.jl exercise.
const EXAMPLE_FIXERS = Set(["abstract-float", "concrete-arg", "constant-array", "unwritten-undef"])

# The names generated packages import: bindings of Base.Iterators that Base does not export.
const ITERATOR_NAMES = ("take", "drop", "cycle", "flatten", "partition", "product")

# How an import statement is written, and whether a `# lint:` comment pins it.
const IMPORT_FORMS = (:using, :import, :trailing_code, :trailing_comment, :opt_out, :other_opt_out, :multiline_opt_out, :block_opt_out)

# Short-form definitions whose `where` binds the return annotation, each with whether it binds an argument.
const WHERE_TEMPLATES = (
    "NAME(x::AbstractVector{T})::AbstractVector{T} where {T} = x" => true,
    "NAME(x::T)::AbstractVector{T} where T<:Real = [x]" => true,
    "NAME(x::T)::AbstractVector{T} where T = [x]" => true,
    "NAME(x::AbstractVector{T})::AbstractVector{T} where {T<:Real} = x" => true,
    "NAME(x::Real)::AbstractVector{T} where T<:Real = T[]" => false,
    "NAME()::AbstractVector{T} where {T} = T[]" => false,
)

# Folds `quadratic-vcat` reports, each with the text the fixer writes for it, or `""` when it leaves it.
const FOLD_TEMPLATES = (
    "reduce(vcat, ([i, i + 1] for i in 1:3); init = Int[])" => "collect(Int, Iterators.flatten([i, i + 1] for i in 1:3))",
    "reduce(vcat, [[1], [2, 3]], init = Int[])" => "collect(Int, Iterators.flatten([[1], [2, 3]]))",
    "reduce(vcat, (reduce(vcat, ([j] for j in 1:i); init = Int[]) for i in 1:3); init = Int[])" =>
        "collect(Int, Iterators.flatten(collect(Int, Iterators.flatten([j] for j in 1:i)) for i in 1:3))",
    "reduce(vcat, [1 => 2, 3 => 4]; init = Any[])" => "",
)

# The paths the root file includes, in order.
const INCLUDED_PATHS = ("a.jl", "sub/b.jl", "sub/c.jl")

"""One generated import statement: the `names` it takes from Base.Iterators, written in `form` (`IMPORT_FORMS`)."""
struct ImportShape
    names::Vector{String}
    form::Symbol
end

"""One generated where-return definition: its `template` (`WHERE_TEMPLATES`), whether it `binds` an argument, and its `opt_out` form."""
struct WhereShape
    template::String
    binds::Bool
    opt_out::Symbol
end

"""One generated fold: its `template` (`FOLD_TEMPLATES`), the text the fixer writes for it (`""` for none), and its `opt_out` form."""
struct FoldShape
    template::String
    fixed::String
    opt_out::Symbol
end

"""A `module` block inside a generated file, with its own `imports` and the names it `uses`."""
struct NestedShape
    imports::Vector{ImportShape}
    uses::Vector{String}
end

"""
One generated file: its imports, the names it uses, its where-return definitions, its folds, its nested
modules, the rule a file-level `# lint:` comment names (`""` for none), and whether the file is read-only.
"""
struct FileShape
    imports::Vector{ImportShape}
    uses::Vector{String}
    definitions::Vector{WhereShape}
    folds::Vector{FoldShape}
    nested::Vector{NestedShape}
    file_opt_out::String
    read_only::Bool
end

"""A generated package: its `root` file, which opens `module Generated`, and the files it includes."""
struct PackageShape
    root::FileShape
    included::Vector{FileShape}
end

"""The `WhereShape` of `template` (`WHERE_TEMPLATES`) with `opt_out`."""
where_shape(template::Pair{String, Bool}, opt_out::Symbol)::WhereShape = WhereShape(first(template), last(template), opt_out)

"""The `FoldShape` of `template` (`FOLD_TEMPLATES`) with `opt_out`."""
fold_shape(template::Pair{String, String}, opt_out::Symbol)::FoldShape = FoldShape(first(template), last(template), opt_out)

"""
Vectors of `elements` at most `longest` long, every length equally likely. `Data.Vectors` keeps a
short vector empty for its first thousands of examples.
"""
(up_to(elements::Data.Possibility{T}, longest::Integer)::Data.Possibility{Vector{T}}) where {T} =
    map(first, Data.Vectors(elements; min_size = longest, max_size = longest), Data.SampledFrom(0:longest))

const NAMES = Data.SampledFrom(ITERATOR_NAMES)
const IMPORT_SHAPES = map(ImportShape, map(vcat, NAMES, up_to(NAMES, 2)), Data.SampledFrom(IMPORT_FORMS))
const WHERE_SHAPES = map(where_shape, Data.SampledFrom(WHERE_TEMPLATES), Data.SampledFrom((:none, :line, :block, :other)))
const FOLD_SHAPES = map(fold_shape, Data.SampledFrom(FOLD_TEMPLATES), Data.SampledFrom((:none, :line, :block, :other)))
const NESTED_SHAPES = map(NestedShape, up_to(IMPORT_SHAPES, 2), up_to(NAMES, 2))
const FILE_SHAPES = map(
    FileShape, up_to(IMPORT_SHAPES, 3), up_to(NAMES, 3), up_to(WHERE_SHAPES, 2), up_to(FOLD_SHAPES, 2), up_to(NESTED_SHAPES, 1),
    Data.SampledFrom(("", "misplaced-import", "quadratic-vcat", "where-return")), Data.Booleans(),
)
const PACKAGE_SHAPES = map(PackageShape, FILE_SHAPES, up_to(FILE_SHAPES, length(INCLUDED_PATHS)))

"""The names `imports` take."""
imported_names(imports::AbstractVector{ImportShape})::Set{String} = Set{String}(name for shape in imports for name in shape.names)

"""
The lines of import `shape` labeled `label`, each paired with whether an opt-out pins it; `file_rule`
is the rule the file's own opt-out names.
"""
function import_lines(shape::ImportShape, label::String, file_rule::String)::Vector{Pair{String, Bool}}
    items = join(unique(shape.names), ", ")
    pinned = file_rule == "misplaced-import"
    statement = "using Base.Iterators: $items"
    forms = Dict{Symbol, Vector{Pair{String, Bool}}}(
        :using => [statement => pinned],
        :import => ["import Base.Iterators: $items" => pinned],
        :trailing_code => ["$statement; const tail_$label = 1" => pinned],
        :trailing_comment => ["$statement  # note" => pinned],
        :opt_out => ["$statement # lint: misplaced-import  kept" => true],
        :other_opt_out => ["$statement # lint: where-return  other" => pinned],
        :multiline_opt_out => ["using Base.Iterators:" => true, "    $items # lint: misplaced-import  kept" => true],
        :block_opt_out => ["# lint: misplaced-import-begin  kept" => true, statement => true, "# lint: misplaced-import-end" => true],
    )
    return forms[shape.form]
end

"""The lines of `imports`, labeled from `label`."""
imports_lines(imports::AbstractVector{ImportShape}, label::String, file_rule::String)::Vector{Pair{String, Bool}} =
    Pair{String, Bool}[line for (position, shape) in enumerate(imports) for line in import_lines(shape, "$(label)_$position", file_rule)]

"""The `const` lines reading each of `uses` that `available` holds, labeled from `label`."""
use_lines(uses::AbstractVector{String}, available::AbstractSet{String}, label::String)::Vector{Pair{String, Bool}} =
    Pair{String, Bool}["const use_$(label)_$position = $name" => false for (position, name) in enumerate(uses) if name in available]

"""
The lines of where-return `shape` labeled `label`. A binding definition an opt-out keeps sits in
`if false`, since its unbound variable fails at load.
"""
function where_lines(shape::WhereShape, label::String, file_rule::String)::Vector{Pair{String, Bool}}
    definition = replace(shape.template, "NAME" => "where_$label")
    opted = shape.opt_out in (:line, :block) || file_rule == "where-return"
    suffixes = Dict(:none => "", :line => " # lint: where-return  kept", :block => "", :other => " # lint: misplaced-import  other")
    body = [definition * suffixes[shape.opt_out] => opted]
    if shape.opt_out === :block
        body = vcat(["# lint: where-return-begin  kept" => true], body, ["# lint: where-return-end" => true])
    end
    if shape.binds && opted
        return vcat(["if false" => false], body, ["end" => false])
    end
    return body
end

"""Whether fold `shape` is kept by a line or block opt-out, or by the file's own opt-out of `quadratic-vcat`."""
fold_opted(shape::FoldShape, file_rule::String)::Bool = shape.opt_out in (:line, :block) || file_rule == "quadratic-vcat"

"""
The lines of fold `shape` labeled `label`, a constant `fold_LABEL`; as the fixer should leave them when
`fixed`, which rewrites a fold no opt-out keeps and the fixer can repair.
"""
function fold_lines(shape::FoldShape, label::String, file_rule::String, fixed::Bool)::Vector{Pair{String, Bool}}
    opted = fold_opted(shape, file_rule)
    call = ifelse(fixed && !opted && !isempty(shape.fixed), shape.fixed, shape.template)
    suffixes = Dict(:none => "", :line => " # lint: quadratic-vcat  kept", :block => "", :other => " # lint: where-return  other")
    body = ["const fold_$label = $call$(suffixes[shape.opt_out])" => opted]
    if shape.opt_out === :block
        return vcat(["# lint: quadratic-vcat-begin  kept" => true], body, ["# lint: quadratic-vcat-end" => true])
    end
    return body
end

"""The lines of nested module `shape` labeled `label`: its imports, and its uses of what they take."""
nested_lines(shape::NestedShape, label::String, file_rule::String)::Vector{Pair{String, Bool}} = vcat(
    ["module Nested_$label" => false], imports_lines(shape.imports, label, file_rule),
    use_lines(shape.uses, imported_names(shape.imports), label), ["end" => false],
)

"""
The body lines of `file` labeled `label`, whose uses read the names of `available`: imports, uses,
where-return definitions, folds (as the fixer should leave them when `fixed`), the `included` lines,
then nested modules.
"""
function body_lines(file::FileShape, label::String, available::AbstractSet{String}, included::AbstractVector{Pair{String, Bool}}, fixed::Bool)::Vector{Pair{String, Bool}}
    rule = file.file_opt_out
    definitions = Pair{String, Bool}[line for (position, shape) in enumerate(file.definitions) for line in where_lines(shape, "$(label)_$position", rule)]
    folds = Pair{String, Bool}[line for (position, shape) in enumerate(file.folds) for line in fold_lines(shape, "$(label)_$position", rule, fixed)]
    nested = Pair{String, Bool}[line for (position, shape) in enumerate(file.nested) for line in nested_lines(shape, "$(label)_$position", rule)]
    opt_out = Pair{String, Bool}[]
    if !isempty(rule)
        opt_out = ["# lint: $rule-file  generated" => true]
    end
    return vcat(opt_out, imports_lines(file.imports, label, rule), use_lines(file.uses, available, label), definitions, folds, included, nested)
end

"""A generated file: its `path` under `src`, its `text`, its `pinned` lines in order, and whether it is `read_only`."""
struct GeneratedFile
    path::String
    text::String
    pinned::Vector{String}
    read_only::Bool
end

"""The `GeneratedFile` at `path` of `lines` (line => pinned)."""
generated_file(path::String, lines::AbstractVector{Pair{String, Bool}}, read_only::Bool)::GeneratedFile =
    GeneratedFile(path, join(first.(lines), "\n") * "\n", first.(filter(last, lines)), read_only)

"""
The files of `package`, with their folds as the fixer should leave them when `fixed`. Uses in the root
read its own imports; an included file reads those of the root and of every file included up to it,
which load before it.
"""
function package_files(package::PackageShape, fixed::Bool)::Vector{GeneratedFile}
    paths = collect(INCLUDED_PATHS[eachindex(package.included)])
    scopes = accumulate(union, vcat([imported_names(package.root.imports)], [imported_names(file.imports) for file in package.included]))
    includes = Pair{String, Bool}["include($(repr(path)))" => false for path in paths]
    root_lines = vcat(["module Generated" => false], body_lines(package.root, "0", first(scopes), includes, fixed), ["end" => false])
    root = generated_file("Generated.jl", root_lines, package.root.read_only)
    included = [
        generated_file(path, body_lines(file, "$position", scope, Pair{String, Bool}[], fixed), file.read_only)
            for (position, (path, file, scope)) in enumerate(zip(paths, package.included, Iterators.drop(scopes, 1)))
    ]
    return vcat([root], included)
end

"""Whether where-return `shape` stays a finding after a fix: it binds no argument and no line or block opt-out keeps it."""
unrepairable(shape::WhereShape)::Bool = !shape.binds && shape.opt_out in (:none, :other)

"""The where-return definitions of `package` no opt-out keeps and no fixer repairs: those binding no argument."""
unrepairable_definitions(package::PackageShape)::Int =
    sum(Int[count(unrepairable, file.definitions) for file in vcat([package.root], package.included) if file.file_opt_out != "where-return"])

"""The files of `package` labeled as `package_files` labels them, in order."""
package_labels(package::PackageShape)::Vector{Pair{String, FileShape}} =
    vcat(["0" => package.root], ["$position" => file for (position, file) in enumerate(package.included)])

"""The folds of `package` no opt-out keeps and the fixer leaves: those it cannot repair."""
unrepairable_folds(package::PackageShape)::Int =
    sum(Int[count(shape -> isempty(shape.fixed) && !fold_opted(shape, file.file_opt_out), file.folds) for file in vcat([package.root], package.included)])

"""Whether every fold constant of `package` in `generated`, its loaded module, holds what its original fold computes."""
fold_values_kept(generated::Module, package::PackageShape)::Bool = all(
    Base.invokelatest(getglobal, generated, Symbol("fold_$(label)_$position")) == Core.eval(Module(), Meta.parse(shape.template))
        for (label, file) in package_labels(package) for (position, shape) in enumerate(file.folds)
)

"""Whether byte `start` falls in one of the byte ranges `ranges`."""
in_ranges(start::Integer, ranges::AbstractVector{<:UnitRange})::Bool = any(Base.Fix1(in, start), ranges)

"""How a token of `text` counts for the token property: `:import`, `:blank`, `:newline`, `:paren`, `:tail` (`;` or a comment) or `:code`."""
function token_class(token::SYNTAX.Token, text::String, imports::AbstractVector{<:UnitRange})::Symbol
    kind = SYNTAX.kind(token)
    if in_ranges(first(token.range), imports)
        return :import
    elseif kind === SYNTAX.@K_str("Whitespace")
        return :blank
    elseif kind === SYNTAX.@K_str("NewlineWs")
        return :newline
    elseif text[token.range] in ("(", ")")
        return :paren
    elseif kind === SYNTAX.@K_str("Comment") || kind === SYNTAX.@K_str(";")
        return :tail
    end
    return :code
end

"""Whether a token of `class` sits after an import on its line, past only blanks, `;` and comments; `before` says so of the token before it."""
follows_import(before::Bool, class::Symbol)::Bool = class === :import || (before && class in (:blank, :tail))

"""
The tokens of `text` a fixer must keep, in order: all but import statements, the `;` and comment that
follow one on its line, blanks, and the parentheses the where-return fixer adds.
"""
function significant_tokens(text::String)::Vector{String}
    imports = SYNTAX.byte_range.(Corset.import_nodes(SYNTAX.parseall(SYNTAX.SyntaxNode, text)))
    tokens = SYNTAX.tokenize(text)
    classes = token_class.(tokens, text, (imports,))
    previous = Iterators.flatten(((false,), accumulate(follows_import, classes; init = false)))
    return String[text[token.range] for (token, class, follows) in zip(tokens, classes, previous) if class === :code || (class === :tail && !follows)]
end

"""How many of `wanted` a greedy in-order scan has `matched` after also reading `line`."""
function matched_after(wanted::AbstractVector{String}, matched::Integer, line::AbstractString)::Int
    if matched < length(wanted) && line == wanted[begin + matched]
        return matched + 1
    end
    return matched
end

"""Whether `wanted` appears in `lines` in order, not necessarily adjacent."""
subsequence(wanted::AbstractVector{String}, lines::AbstractVector{<:AbstractString})::Bool =
    foldl(Base.Fix1(matched_after, wanted), lines; init = 0) == length(wanted)

"""The text of every file of `files` under the `src` of `root`, in order."""
file_texts(root::String, files::AbstractVector{GeneratedFile})::Vector{String} = [read(joinpath(root, "src", file.path), String) for file in files]

"""The Project.toml of a generated package: it turns on exactly the fixable rules, at `deny`."""
function fixer_project()::String
    levels = Dict(check.name => ifelse(Corset.fixable(rule), "deny", "allow") for rule in Corset.RULES for check in Corset.checks(rule))
    return sprint(TOML.print, Dict("preferences" => Dict("Corset" => Dict("levels" => levels))))
end

"""
Whether `corset check --fix` on `package` keeps every fixer property: each file parses and keeps its
mode and significant tokens; pinned lines stay in order; the package loads; the fixed rules report only
the definitions and folds no fixer can repair; every fold constant keeps its value; and a second fix
changes nothing. Significant tokens are compared with the package as the fixer should leave it, folds
rewritten.
"""
function fix_keeps_properties(package::PackageShape)::Bool
    root = mktempdir()
    files = package_files(package, false)
    expected = package_files(package, true)
    paths = [joinpath(root, "src", file.path) for file in files]
    mkpath.(dirname.(paths))
    write.(paths, [file.text for file in files])
    chmod.(paths, ifelse.([file.read_only for file in files], 0o444, 0o644))
    modes = filemode.(paths)
    write(joinpath(root, "Project.toml"), fixer_project())
    config = Corset.load_config(root)
    findings, _ = Corset.run_rules(config, root; fix = true)
    fixed = file_texts(root, files)
    SYNTAX.parseall.(SYNTAX.SyntaxNode, fixed)
    loaded = Module()
    Base.include(loaded, joinpath(root, "src", "Generated.jl"))
    rules = [finding.rule for finding in findings]
    second, _ = Corset.run_rules(config, root; fix = true)
    return filemode.(paths) == modes &&
        significant_tokens.([file.text for file in expected]) == significant_tokens.(fixed) &&
        all(subsequence.([file.pinned for file in files], split.(fixed, '\n'))) &&
        count(==("misplaced-import"), rules) == 0 &&
        count(==("where-return"), rules) == unrepairable_definitions(package) &&
        count(==("quadratic-vcat"), rules) == unrepairable_folds(package) &&
        fold_values_kept(Base.invokelatest(getglobal, loaded, :Generated), package) &&
        [finding.rule for finding in second] == rules &&
        file_texts(root, files) == fixed
end

@testset "fixers: generated packages keep every fixer property" begin
    @test Set(Corset.rule_name.(filter(Corset.fixable, Corset.RULES))) == union(GENERATED_FIXERS, EXAMPLE_FIXERS)
    report = @check max_examples = 300 db = false function fixed_package(package = PACKAGE_SHAPES)
        fix_keeps_properties(package)
    end
    @test Supposition.results(report).ispass
end

using InteractiveUtils: subtypes

# The rules the `corset` command runs, each a singleton type whose name, group, summary and check
# are methods. The library functions stay callable on their own; a rule here fixes their arguments.

"""
    Context(repository, directories, mod; inferred = Inferred[], candidates = CandidateSearch(inferred), own_methods = defined_methods(mod))

Everything a rule reads: the repository, the source directories that exist, the loaded package, its
inferred frames, the `CandidateSearch` the typed rules share, the package's `defined_methods`, the `Source` of every Julia file
under `directories`, each parsed once here and read by every rule, and the `# lint:` `comments` of
those files and of the frames' files (`frame_comments`), by path.
"""
struct Context
    repository::Repository
    directories::Tuple{Vararg{String}}
    mod::Union{Module, Nothing}
    inferred::Vector{Inferred}
    candidates::CandidateSearch
    own_methods::Vector{Method}
    sources::Vector{Source}
    comments::Dict{String, Vector{OptOutComment}}
    parse_errors::Vector{Finding}
end

function Context(
        repository::Repository, directories::Tuple{Vararg{AbstractString}}, mod::Union{Module, Nothing};
        inferred::AbstractVector{Inferred} = Inferred[], candidates::CandidateSearch = CandidateSearch(inferred),
        own_methods::AbstractVector{Method} = defined_methods(mod),
    )::Context
    sources, parse_errors = parsed_sources(repository, directories)
    parsed = Dict{String, Vector{OptOutComment}}(source.path => source.comments for source in sources)
    return Context(repository, directories, mod, inferred, candidates, own_methods, sources, merge(parsed, frame_comments(repository, inferred, parsed)), parse_errors)
end

"""
The parsed Julia files under `directories` of `repository` (`repository_sources`), and a deny-level
`parse-error` finding for each file that does not parse, at its first error. Each file is parsed once,
by `Source`.
"""
function parsed_sources(repository::Repository, directories::Tuple{Vararg{String}})::Tuple{Vector{Source}, Vector{Finding}}
    sources = Source[]
    failures = Finding[]
    for path in repository_sources(repository, directories)
        try
            push!(sources, Source(repository, path))
        catch error_
            if error_ isa SYNTAX.ParseError # lint: non-public-access  `parseall` throws it, and Base exports no public name for it
                push!(failures, parse_error_finding(repository, path, error_))
            else
                rethrow() # COV_EXCL_LINE
            end
        end
    end
    return sources, failures
end

"""The `parse-error` finding for file `path` of `repository`, at the first error `failure` reports."""
function parse_error_finding(repository::Repository, path::AbstractString, failure::SYNTAX.ParseError)::Finding # lint: non-public-access  `parseall` throws it, and Base exports no public name for it
    diagnostic = first(Iterators.filter(diagnostic -> diagnostic.level === :error, failure.diagnostics))
    line = SYNTAX.source_line(failure.source, SYNTAX.first_byte(diagnostic))
    return Finding("parse-error", :deny, Site(file_key(repository, path), path, line, diagnostic.message))
end

"""
A check with a name, a group (`:default` or `:pedantic`) and a one-line summary. The subtypes say
what it reads: `ModuleRule` the loaded package, `TreeRule` the source directories as a whole,
`FileRule` one parsed file at a time.
"""
abstract type Rule end
abstract type ModuleRule <: Rule end
abstract type TreeRule <: Rule end
abstract type FileRule <: Rule end

"""The name of `rule` in baselines, opt-out comments and configuration."""
function rule_name end

"""`:default` for a likely defect or a pattern Rust rejects without an explicit marker; `:pedantic` for house style or a noisy heuristic."""
function rule_group end

"""One line saying what `rule` finds."""
function rule_summary end

"""
    check(rule, context)
    check(rule, context, source)

The `Site`s `rule` finds: in the whole `context` for a `ModuleRule` or `TreeRule`, in the parsed file
`source` for a `FileRule`.
"""
function check end

"""
    fix_plan(rule, repository, directories)

The `FixPlan` that rewrites the Julia files under `directories` of `repository` so `rule` finds nothing.
Only a fixable rule has a method. A plan writes nothing; `fix!` applies it.
"""
function fix_plan end

"""Whether `rule` has a `fix_plan`."""
fixable(rule::Rule)::Bool = hasmethod(fix_plan, Tuple{typeof(rule), Repository, Tuple{Vararg{String}}})

"""
    fix!(rule, repository, directories)

Apply the `fix_plan` of `rule` (`apply_plan!`): every repair except those a `# lint:` comment naming
`rule` opts out. Returns the sites repaired.
"""
fix!(rule::Rule, repository::Repository, directories::Tuple{Vararg{String}})::Vector{Site} =
    apply_plan!(fix_plan(rule, repository, directories), rule_name(rule))

# The parameters a rule's body names, by what the rule reads.
const RULE_PARAMETERS = (;
    ModuleRule = (Pair{Symbol, Any}(:context, :Context),),
    TreeRule = (Pair{Symbol, Any}(:context, :Context),),
    FileRule = (Pair{Symbol, Any}(:context, :Context), Pair{Symbol, Any}(:source, :Source)),
)

"""
    @rule Kind "name" :group "summary" (context, source) -> body

Define the rule `name` (a `ModuleRule`, `TreeRule` or `FileRule`) whose `check` is `body`, with the
parameters of its kind bound as written: `context` for the first two, `context` and `source` for
a `FileRule`. The type is the rule name in CamelCase with `Rule` appended.
"""
macro rule(kind, name, group, summary, definition)
    parameters::Vector{Union{Symbol, Expr}} = [definition.args[1]]
    if definition.args[1] isa Expr
        parameters = definition.args[1].args
    end
    expected::Vector{Symbol} = collect(first.(RULE_PARAMETERS[kind]))
    if parameters != expected
        error("a $kind takes the parameters $(Tuple(expected)), not $(Tuple(parameters))")
    end
    type = Symbol(join(titlecase.(split(name, '-'))), "Rule")
    arguments::Vector{Expr} = [:($parameter::$annotation) for (parameter, annotation) in RULE_PARAMETERS[kind]]
    return esc(
        quote
            struct $type <: $kind end
            rule_name(::$type)::String = $name
            rule_group(::$type)::Symbol = $group
            rule_summary(::$type)::String = $summary
            check(::$type, $(arguments...))::Vector{Site} = $(definition.args[2])
        end
    )
end

"""Every struct the package defines with the file and line it is declared at, for placing a struct rule's sites."""
declared(context::Context)::Vector{StructDeclaration} = struct_locations(context.sources)

"""The scope a `FileRule` resolves type names in: the loaded package, or `Base` when none is loaded."""
scope(context::Context)::Module = something(context.mod, Base)

"""The loaded package of `context`, which a module rule reads; `can_run` runs one only when there is one."""
function loaded_module(context::Context)::Module
    mod = context.mod
    if isnothing(mod)
        throw(ArgumentError("a module rule ran on a context with no loaded package; `can_run` should have skipped it"))
    end
    return mod
end

@rule ModuleRule "hidden-input" :default "reads of a mutable or non-constant global, or a ScopedValue" context ->
hidden_inputs(context.repository, loaded_module(context); context.own_methods)

@rule ModuleRule "non-public-access" :default "qualified accesses and explicit imports of another module's non-public names" context ->
non_public_accesses(loaded_module(context))

@rule ModuleRule "abstract-local" :default "local variables whose inferred type is abstract or a union" context ->
abstract_locals(context.repository, context.inferred; context.comments)

@rule ModuleRule "bang" :default "functions that always return nothing and have no ! in the name" context ->
unmarked_effects(context.repository, context.inferred)

@rule ModuleRule "unmarked-mutation" :default "functions without ! in the name that write through an argument" context ->
unmarked_mutations(context.repository, context.inferred; search = context.candidates)

@rule ModuleRule "runtime-dispatch" :default "calls left to run-time dispatch in the frames the signatures compile" context ->
runtime_dispatches(context.repository, context.inferred; context.comments)

@rule ModuleRule "recursion-limit" :default "calls inference cuts off at its recursion limit, their argument types nesting deeper with every call" context ->
recursion_limits(context.repository, context.inferred, loaded_module(context); context.comments)

@rule ModuleRule "float-widening" :default "statements whose float result is wider than every float argument of their method" context ->
float_widenings(context.repository, context.inferred; search = context.candidates, context.comments)

@rule ModuleRule "widened-return" :default "methods whose inferred result a caller cannot compile against concretely" context ->
widened_returns(context.repository, context.inferred; context.comments)

@rule ModuleRule "jet" :default "JET.report_call's error reports on the frames the signatures compile (JET installed)" context ->
call_report_sites(context.repository, context.inferred, loaded_module(context); context.comments)

@rule ModuleRule "impure-anonymous-function" :default "anonymous functions that capture mutable state, rebind a capture, or were never compiled (and, with strict_captures, any capture)" context ->
impure_anonymous_functions(context.repository, loaded_module(context); context.own_methods)

@rule ModuleRule "unstable-anonymous-function" :default "anonymous functions whose captures inference leaves abstract" context ->
unstable_anonymous_functions(context.repository, loaded_module(context); context.own_methods)

@rule ModuleRule "overspecialized-anonymous-function" :default "anonymous functions that capture a type or function, compiling once per value" context ->
overspecialized_anonymous_functions(context.repository, loaded_module(context); context.own_methods)

"""The sites of the struct `types`, each placed at its declaration in `context`'s sources."""
struct_sites(types::AbstractVector{DataType}, context::Context)::Vector{Site} = struct_site.(types, (declared(context),))

@rule ModuleRule "abstract-field" :default "struct fields of an abstract type or of a container of one" context ->
struct_sites(filter(!isempty ∘ abstract_fields, module_structs(loaded_module(context))), context)

@rule ModuleRule "mutable-struct" :default "structs declared with the mutable keyword" context ->
struct_sites(mutable_structs(loaded_module(context)), context)

@rule ModuleRule "wide-struct" :pedantic "structs with more fields than the repository's struct_field_limit" context ->
struct_sites(filter(Base.Fix2(wider_struct, context.repository.struct_field_limit), module_structs(loaded_module(context))), context)

@rule ModuleRule "struct-constant" :pedantic "constants that hold a struct of the package, which Revise leaves stale after an edit" context ->
struct_holding_constants(loaded_module(context))

@rule ModuleRule "repeated-prefix" :pedantic "field names that repeat a word the type should say once" context ->
struct_sites(filter(!isnothing ∘ repeated_prefix, module_structs(loaded_module(context))), context)

@rule FileRule "nothing-return" :pedantic "declared Union{Nothing, …} results" (context, source) ->
nothing_returns(source)

@rule FileRule "range-guard" :pedantic "floatmin/floatmax and exp range edges used as overflow guards" (context, source) ->
range_guards(source)

@rule FileRule "repeated-statement" :default "a statement repeated in one block" (context, source) ->
repeated_statements(source)

@rule FileRule "return-type" :default "calls of Core.Compiler.return_type" (context, source) ->
return_type_calls(source)

@rule FileRule "concrete-arg" :default "arguments annotated with a concrete container the method never resizes" (context, source) ->
concrete_arguments(source)

@rule FileRule "concrete-return" :pedantic "results annotated with a concrete type" (context, source) ->
concrete_returns(source, scope(context))

@rule FileRule "annotation" :default "methods with an unannotated argument or result" (context, source) ->
missing_annotations(source)

@rule FileRule "float64" :pedantic "Float64 tokens and untyped float literals" (context, source) ->
float64_sites(source)

@rule FileRule "c-type" :pedantic "C-interop types (Cint, Cdouble, ...) outside a ccall" (context, source) ->
c_type_sites(source)

@rule FileRule "ref" :pedantic "Ref and RefValue outside a ccall, state carried by reference" (context, source) ->
ref_sites(source)

@rule FileRule "one-letter" :pedantic "one-letter variable names" (context, source) ->
one_letter_sites(context.repository, source)

@rule FileRule "file-length" :pedantic "source files longer than the repository's file_line_limit" (context, source) ->
long_file_sites(context.repository, source)

@rule FileRule "derived-constant" :default "constants computed by a function of the package, which Revise leaves stale after an edit" (context, source) ->
derived_constant_sites(context.mod, source)

@rule FileRule "forbidden-pattern" :default "lines that match a pattern the project forbids (forbidden_patterns)" (context, source) ->
forbidden_pattern_sites(context.repository, source)

@rule FileRule "where-return" :default "short-form definitions whose where binds the return annotation" (context, source) ->
where_return_sites(source)

@rule TreeRule "constant-array" :pedantic "zeros, ones, fill, trues and falses of an array no code writes, which FillArrays stores as one value" context ->
constant_array_sites(context.sources)

@rule FileRule "broad-catch" :default "catch blocks that handle every exception alike, rethrowing none" (context, source) ->
broad_catches(source)

@rule FileRule "quadratic-scan" :pedantic "loops over a collection that scan the same collection per element" (context, source) ->
quadratic_scans(source)

@rule FileRule "quadratic-vcat" :default "folds that concatenate one piece at a time: reduce(vcat, …; init), foldl(vcat, …), mapreduce(f, vcat, …)" (context, source) ->
quadratic_concatenations(source)

@rule FileRule "non-atomic-write" :default "loops and broadcasts that write several files in turn, unstaged" (context, source) ->
non_atomic_writes(source)

@rule TreeRule "misplaced-import" :default "imports their file does not use, or that only other files use" context ->
misplaced_imports(context.repository, context.sources)

@rule TreeRule "fatou" :default "findings of fatou lint (fatou on PATH)" context ->
fatou_sites(context.repository, context.directories)

@rule TreeRule "jscpd" :pedantic "findings of jscpd duplicate code checks (jscpd on PATH)" context ->
jscpd_sites(context.repository, context.directories)

fix_plan(::MisplacedImportRule, repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ImportMove, PlacedTexts} =
    import_plan(repository, directories)

fix_plan(::WhereReturnRule, repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{WhereParentheses, typeof(parenthesized_texts)} =
    where_plan(repository, directories)

fix_plan(::ConstantArrayRule, repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{FillRewrite, typeof(filled_texts)} =
    constant_array_plan(repository, directories, false)

fix_plan(::QuadraticVcatRule, repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)} =
    flatten_plan(repository, directories)

fix_plan(::ConcreteArgRule, repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)} =
    concrete_arg_plan(repository, directories)

"""Every rule, ordered by name."""
const RULES = Tuple(sort!([type() for kind in (ModuleRule, TreeRule, FileRule) for type in subtypes(kind)]; by = rule_name))

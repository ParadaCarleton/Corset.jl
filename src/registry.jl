using InteractiveUtils: subtypes

# The rules the `corset` command runs, each a singleton type whose name, group, summary and check
# are methods. The library functions stay callable on their own; a rule here fixes their arguments.

"""
    Context(repository, directories, mod; inferred = Inferred[], candidates = CandidateSearch(inferred))

Everything a rule reads: the repository, the source directories that exist, the loaded package, its
inferred frames, the `CandidateSearch` the typed rules share, and the `Source` of every Julia file
under `directories`, each parsed once here and read by every rule.
"""
struct Context
    repository::Repository
    directories::Tuple{Vararg{String}}
    mod::Union{Module, Nothing}
    inferred::Vector{Inferred}
    candidates::CandidateSearch
    sources::Vector{Source}
end

function Context(
        repository::Repository, directories::Tuple{Vararg{AbstractString}}, mod::Union{Module, Nothing};
        inferred::AbstractVector{Inferred} = Inferred[], candidates::CandidateSearch = CandidateSearch(inferred),
    )::Context
    return Context(repository, directories, mod, inferred, candidates, Source.(repository_sources(repository, directories)))
end

"""The `# lint:` comments of each file `context` parsed, by path."""
source_comments(context::Context)::Dict{String, Vector{OptOutComment}} =
    Dict{String, Vector{OptOutComment}}(source.path => source.comments for source in context.sources)

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

"""`:default` for a rule that finds likely defects, `:pedantic` for one that enforces a style."""
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
    fix!(rule, repository, directories)

Rewrite the Julia files under `directories` of `repository` so `rule` finds nothing. Only a `fixable`
rule has a method.
"""
function fix! end

"""Whether `rule` has a `fix!`."""
fixable(::Rule)::Bool = false

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

@rule ModuleRule "hidden-input" :default "reads of a mutable or non-constant global, or a ScopedValue" context ->
hidden_inputs(context.mod)

@rule ModuleRule "non-public-access" :pedantic "qualified accesses and explicit imports of another module's non-public names" context ->
non_public_accesses(context.mod)

@rule ModuleRule "abstract-local" :default "local variables whose inferred type is abstract or a union" context ->
abstract_locals(context.repository, context.inferred)

@rule ModuleRule "bang" :pedantic "functions that always return nothing and have no ! in the name" context ->
unmarked_effects(context.repository, context.inferred)

@rule ModuleRule "unmarked-mutation" :pedantic "functions without ! in the name that write through an argument" context ->
unmarked_mutations(context.repository, context.inferred; search = context.candidates)

@rule ModuleRule "runtime-dispatch" :pedantic "calls left to run-time dispatch in the frames the signatures compile" context ->
runtime_dispatches(context.repository, context.inferred)

@rule ModuleRule "float-widening" :pedantic "statements whose float result is wider than every float argument of their method" context ->
float_widenings(context.repository, context.inferred; search = context.candidates)

@rule ModuleRule "widened-return" :pedantic "methods whose inferred result a caller cannot compile against concretely" context ->
widened_returns(context.repository, context.inferred)

@rule ModuleRule "impure-anonymous-function" :default "anonymous functions that capture mutable state, rebind a capture, or were never compiled" context ->
impure_anonymous_functions(context.mod)

@rule ModuleRule "unstable-anonymous-function" :default "anonymous functions whose captures inference leaves abstract" context ->
unstable_anonymous_functions(context.mod)

@rule ModuleRule "overspecialized-anonymous-function" :default "anonymous functions that capture a type or function, compiling once per value" context ->
overspecialized_anonymous_functions(context.mod)

"""The sites of the struct `types`, each placed at its declaration in `context`'s sources."""
struct_sites(types::AbstractVector{DataType}, context::Context)::Vector{Site} = struct_site.(types, (declared(context),))

@rule ModuleRule "abstract-field" :default "struct fields of an abstract type or of a container of one" context ->
struct_sites(filter(!isempty ∘ abstract_fields, module_structs(context.mod)), context)

@rule ModuleRule "mutable-struct" :default "structs declared with the mutable keyword" context ->
struct_sites(mutable_structs(context.mod), context)

@rule ModuleRule "repeated-prefix" :pedantic "field names that repeat a word the type should say once" context ->
struct_sites(filter(!isnothing ∘ repeated_prefix, module_structs(context.mod)), context)

@rule FileRule "nothing-return" :pedantic "declared Union{Nothing, …} results" (context, source) ->
nothing_returns(source)

@rule FileRule "range-guard" :pedantic "floatmin/floatmax and exp range edges used as overflow guards" (context, source) ->
range_guards(source)

@rule FileRule "repeated-statement" :default "a statement repeated in one block" (context, source) ->
repeated_statements(source)

@rule FileRule "return-type" :pedantic "calls of Core.Compiler.return_type" (context, source) ->
return_type_calls(source)

@rule FileRule "concrete-arg" :pedantic "arguments annotated with a concrete container the method never resizes" (context, source) ->
concrete_arguments(source)

@rule FileRule "concrete-return" :pedantic "results annotated with a concrete type" (context, source) ->
concrete_returns(source, scope(context))

@rule FileRule "annotation" :pedantic "methods with an unannotated argument or result" (context, source) ->
missing_annotations(source)

@rule FileRule "float64" :pedantic "Float64 tokens and untyped float literals" (context, source) ->
float64_sites(source)

@rule FileRule "c-type" :pedantic "C-interop types (Cint, Cdouble, ...) outside a ccall" (context, source) ->
c_type_sites(source)

@rule FileRule "ref" :pedantic "Ref and RefValue outside a ccall, state carried by reference" (context, source) ->
ref_sites(source)

@rule FileRule "one-letter" :pedantic "one-letter variable names" (context, source) ->
one_letter_sites(context.repository, source)

@rule FileRule "where-return" :default "short-form definitions whose where binds the return annotation" (context, source) ->
where_return_sites(source)

@rule TreeRule "misplaced-import" :default "imports their file does not use, or that only other files use" context ->
misplaced_imports(context.repository, context.directories)

@rule TreeRule "fatou" :pedantic "findings of fatou lint (fatou on PATH)" context ->
fatou_sites(context.repository, context.directories)

@rule TreeRule "jscpd" :pedantic "findings of jscpd duplicate code checks (jscpd on PATH)" context ->
jscpd_sites(context.repository, context.directories)

fixable(::MisplacedImportRule)::Bool = true
fix!(::MisplacedImportRule, repository::Repository, directories::Tuple{Vararg{String}})::Nothing = (place_imports!(repository, directories); nothing)

fixable(::WhereReturnRule)::Bool = true
fix!(::WhereReturnRule, repository::Repository, directories::Tuple{Vararg{String}})::Nothing = (fix_where_returns!(repository, directories); nothing)

"""Every rule, ordered by name."""
const RULES = Tuple(sort!([type() for kind in (ModuleRule, TreeRule, FileRule) for type in subtypes(kind)]; by = rule_name))

# Constants Revise cannot keep current: Revise rebuilds a revised struct and re-evaluates a constant only
# when its own text changes, so a constant that holds a struct of the package, or is computed by one of
# its functions, keeps the old definition after an edit.

"""Whether `module_` is `owner` or one of its submodules."""
within(module_::Module, owner::Module)::Bool = module_ === owner || (parentmodule(module_) !== module_ && within(parentmodule(module_), owner))

"""Whether `type` is a generic function's type, whose methods Revise tracks; its name starts with `#`."""
function_type(type::DataType)::Bool = type <: Function && startswith(string(type.name.name), "#")

"""Whether `type`, its parameters (types or instances), a type variable's bound or a member of a `Union` in it is a struct defined in `owner`."""
function names_own_struct(@nospecialize(type::Any), owner::Module)::Bool
    if type isa TypeVar
        return names_own_struct(type.ub, owner) || names_own_struct(type.lb, owner)
    elseif type isa UnionAll
        return names_own_struct(type.var, owner) || names_own_struct(type.body, owner)
    elseif type isa Union
        return names_own_struct(type.a, owner) || names_own_struct(type.b, owner)
    elseif type isa Core.TypeofVararg
        return isdefined(type, :T) && names_own_struct(type.T, owner)
    elseif !(type isa Type)
        return names_own_struct(typeof(type), owner) # an instance as a parameter, as in `Val{Setting(1)}`
    elseif !(type isa DataType)
        return false
    elseif isstructtype(type) && !function_type(type) && within(parentmodule(type), owner)
        return true
    end
    return any(Base.Fix2(names_own_struct, owner), type.parameters)
end

"""
Whether `data` holds a struct defined in `owner`: as its own type, a type parameter, a field, an
element, or a type it carries as data. The walk stops at `depth` levels, enough for nested settings,
and at a `Task`, whose captured state belongs to the code it runs.
"""
function holds_own_struct(@nospecialize(data::Any), owner::Module, depth::Integer)::Bool # lint: impure-anon-fun # lint: unstable-anon-fun  the generators only read `owner` and `data`
    if data isa Type
        return names_own_struct(data, owner)
    elseif names_own_struct(typeof(data), owner)
        return true
    elseif depth == 0 || isbitstype(typeof(data)) || data isa Task
        return false
    elseif data isa Union{AbstractArray, AbstractSet, AbstractDict}
        # A concrete element type can still hold anything (a `Pair` with an abstract value type); only bits types cannot.
        return !isbitstype(eltype(data)) && any(holds_own_struct(element, owner, depth - 1) for element in data)::Bool # lint: runtime-dispatch  reflects on values of unknown type
    end
    return isstructtype(typeof(data)) &&
        any(holds_own_struct(getfield(data, index), owner, depth - 1) for index in 1:nfields(data) if isdefined(data, index))::Bool
end

"""
Whether `data`, bound to `name` in `module_`, is the definition of that type (a struct, abstract type or
enum) and no alias of it. Moshi's `@data Name` defines struct `typeof(Name)` and `const Type` to it in one
expansion, which Revise replays whole, so that `Type` counts as a definition.
"""
function type_definition(module_::Module, name::Symbol, data::Type)::Bool
    unwrapped = Base.unwrap_unionall(data)
    moshi_name = Symbol("typeof(", nameof(module_), ")")
    return unwrapped isa DataType && parentmodule(unwrapped) === module_ &&
        (nameof(unwrapped) === name || (name === :Type && nameof(unwrapped) === moshi_name))
end

"""Whether the constant `name` of `module_`, bound to `data`, is a module, a function or a type definition: what a constant may be."""
function definition_binding(module_::Module, name::Symbol, @nospecialize(data::Any))::Bool
    return data isa Module || (data isa Function && function_type(typeof(data))) || (data isa Type && type_definition(module_, name, data))
end

"""
The constants of `mod`'s package, as sites keyed `Module.name`, that hold a struct the package defines
(`holds_own_struct`): an instance, or an alias of a type naming one (`const Alias = Union{Nothing, Setting}`).
Definitions of types, modules and functions pass.
"""
function struct_holding_constants(mod::Module)::Vector{Site} # lint: impure-anon-fun  the generators only read the modules
    bindings = [ # lint: unstable-variable  reflects on values of unknown type
        (module_, name, getglobal(module_, name)) for module_ in Membership.package_modules(Membership.Package(mod))
            for name in names(module_; all = true)
            if !startswith(string(name), "#") && isconst(module_, name) && isdefinedglobal(module_, name)
    ]
    return [ # lint: runtime-dispatch  reflects on values of unknown type
        Site(string(module_, ".", name), "", 0, "holds a struct of $(nameof(mod)); build it in a function instead")
            for (module_, name, data) in bindings
            if !definition_binding(module_, name, data) && holds_own_struct(data, mod, 6)
    ]
end

"""Each top-level statement of `source` beside the one before it, which is its line marker when it has one."""
function top_level_pairs(source::Source)::Vector{Pair{Any, Any}}
    statements = (Meta.parseall(source.text; filename = source.path)::Expr).args # lint: unstable-variable  Expr nodes hold untyped arguments
    return Pair{Any, Any}.(statements[begin:(end - 1)], statements[(begin + 1):end])
end

"""`statement` without the docstring `@doc` attaches to it."""
function undocumented(@nospecialize(statement::Any))::Any # lint: unmarked-mutation # lint: unstable-return  Expr nodes hold untyped arguments
    if statement isa Expr && statement.head === :macrocall && first(statement.args) == GlobalRef(Core, Symbol("@doc")) # lint: runtime-dispatch  Expr nodes hold untyped arguments
        return last(statement.args)
    end
    return statement
end

"""Whether `statement` is `const NAME = value`."""
is_constant(@nospecialize(statement::Any))::Bool = # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    statement isa Expr && statement.head === :const && first(statement.args) isa Expr && first(statement.args).head === :(=)

"""Whether `name` is bound in `owner` to a function `owner` defines."""
own_function(name::Symbol, owner::Module)::Bool = # lint: runtime-dispatch  reflects on values of unknown type
    isdefinedglobal(owner, name) && getglobal(owner, name) isa Function && parentmodule(getglobal(owner, name)) === owner

"""Whether `qualifier` is a name `owner` binds to itself, as `IRVExtremism` in `IRVExtremism.f`."""
names_module(@nospecialize(qualifier::Any), owner::Module)::Bool = qualifier isa Symbol && isdefinedglobal(owner, qualifier) && getglobal(owner, qualifier) === owner

"""Whether callee `callee` names a function `owner` defines, bare (`f`) or qualified by `owner` (`Owner.f`)."""
own_callee(callee::Symbol, owner::Module)::Bool = own_function(callee, owner)
own_callee(callee::Expr, owner::Module)::Bool = # lint: runtime-dispatch # lint: unmarked-mutation  Expr nodes hold untyped arguments
    callee.head === :. && names_module(first(callee.args), owner) && last(callee.args) isa QuoteNode && own_callee(last(callee.args).value, owner)
own_callee(@nospecialize(::Any), ::Module)::Bool = false

"""Whether expression `value` calls, at any depth, a function that `owner` defines; a function body or quote defers its calls."""
function calls_own_function(@nospecialize(value::Any), owner::Module)::Bool
    if !(value isa Expr) || value.head in (:->, :function, :quote)
        return false
    end
    if value.head === :call && own_callee(first(value.args), owner)
        return true
    end
    return any(Base.Fix2(calls_own_function, owner), value.args)
end

"""
The constants of `source`, as sites keyed `file NAME`, whose value calls a function `owner` defines. Revise
re-evaluates a constant only when its own text changes, so it keeps that function's old result.
"""
function derived_constants(source::Source, owner::Module)::Vector{Site}
    derived = filter(Base.Fix2(is_derived, owner), top_level_pairs(source))
    return derived_site.((source,), derived, (owner,))
end

"""Whether `marked`, a line marker and the statement after it, is a constant whose value calls a function `owner` defines."""
is_derived(marked::Pair{Any, Any}, owner::Module)::Bool = first(marked) isa LineNumberNode && is_constant(undocumented(last(marked))) && # lint: runtime-dispatch  Expr nodes hold untyped arguments
    calls_own_function(first(undocumented(last(marked)).args).args[2], owner)

"""The `derived_constants` site of `marked`, a line marker and the constant after it, in `source`."""
function derived_site(source::Source, marked::Pair{Any, Any}, owner::Module)::Site # lint: unmarked-mutation  Expr nodes hold untyped arguments
    name = first(undocumented(last(marked)).args).args[1] # lint: unstable-variable # lint: runtime-dispatch  Expr nodes hold untyped arguments
    return Site("$(source.name) $name", source.path, first(marked).line, "computed by a function of $(nameof(owner)); define a function instead") # lint: runtime-dispatch  Expr nodes hold untyped arguments
end

"""The `derived_constants` of `source` in the package `mod`; none when no package is loaded."""
derived_constant_sites(::Nothing, ::Source)::Vector{Site} = Site[]
derived_constant_sites(mod::Module, source::Source)::Vector{Site} = derived_constants(source, mod)

"""Whether struct `type` has more than `limit` fields."""
wider_struct(type::DataType, limit::Integer)::Bool = fieldcount(type) > limit

"""
The lines of `source` that match a `ForbiddenPattern` of `repository` (and not its `unless`), as sites
keyed `file pattern-name` at their line, so a baseline allows a count per file and pattern.
"""
function forbidden_pattern_sites(repository::Repository, source::Source)::Vector{Site} # lint: unmarked-mutation  the patterns are a tuple of any length
    lines = split(source.text, '\n')
    return collect(Site, Iterators.flatten(pattern_sites.((source,), (lines,), repository.forbidden_patterns))) # lint: runtime-dispatch  the patterns are a tuple of any length
end

"""The `forbidden_pattern_sites` of `forbidden` among `lines`, the lines of `source`; none in a file it skips."""
function pattern_sites(source::Source, lines::AbstractVector{<:AbstractString}, forbidden::ForbiddenPattern)::Vector{Site}
    if source.name in forbidden.skip_files
        return Site[]
    end
    numbers = findall(Base.Fix1(forbidden_line, forbidden), lines)
    return Site.(("$(source.name) $(forbidden.name)",), (source.path,), numbers, (forbidden.message,))
end

"""Whether `line` matches the pattern of `forbidden` and not its `unless`."""
forbidden_line(forbidden::ForbiddenPattern, line::AbstractString)::Bool =
    occursin(forbidden.pattern, line) && (isnothing(forbidden.unless) || !occursin(forbidden.unless, line))

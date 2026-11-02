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
    return any(names_own_struct(parameter, owner) for parameter in type.parameters)
end

"""
Whether `data` holds a struct defined in `owner`: as its own type, a type parameter, a field, an
element, or a type it carries as data. The walk stops at `depth` levels, enough for nested settings,
and at a `Task`, whose captured state belongs to the code it runs.
"""
function holds_own_struct(@nospecialize(data::Any), owner::Module, depth::Integer)::Bool
    if data isa Type
        return names_own_struct(data, owner)
    elseif names_own_struct(typeof(data), owner)
        return true
    elseif depth == 0 || isbitstype(typeof(data)) || data isa Task
        return false
    elseif data isa Union{AbstractArray, AbstractSet, AbstractDict}
        # A concrete element type can still hold anything (a `Pair` with an abstract value type); only bits types cannot.
        return !isbitstype(eltype(data)) && any(holds_own_struct(element, owner, depth - 1) for element in data)
    end
    return isstructtype(typeof(data)) &&
        any(holds_own_struct(getfield(data, index), owner, depth - 1) for index in 1:nfields(data) if isdefined(data, index))
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
function struct_holding_constants(mod::Module)::Vector{Site}
    bindings = [
        (module_, name, getglobal(module_, name)) for module_ in Membership.package_modules(Membership.Package(mod))
            for name in names(module_; all = true)
            if !startswith(string(name), "#") && isconst(module_, name) && isdefinedglobal(module_, name)
    ]
    return [
        Site(string(module_, ".", name), "", 0, "holds a struct of $(nameof(mod)); build it in a function instead")
            for (module_, name, data) in bindings
            if !definition_binding(module_, name, data) && holds_own_struct(data, mod, 6)
    ]
end

"""Each top-level statement of `source` beside the one before it, which is its line marker when it has one."""
function top_level_pairs(source::Source)::Base.Iterators.Zip
    statements = Meta.parseall(source.text; filename = source.path).args
    return zip(statements, Iterators.drop(statements, 1))
end

"""`statement` without the docstring `@doc` attaches to it."""
function undocumented(@nospecialize(statement::Any))::Any
    if statement isa Expr && statement.head === :macrocall && first(statement.args) == GlobalRef(Core, Symbol("@doc"))
        return last(statement.args)
    end
    return statement
end

"""Whether `statement` is `const NAME = value`."""
is_constant(@nospecialize(statement::Any))::Bool =
    statement isa Expr && statement.head === :const && first(statement.args) isa Expr && first(statement.args).head === :(=)

"""Whether `name` is bound in `owner` to a function `owner` defines."""
own_function(name::Symbol, owner::Module)::Bool =
    isdefinedglobal(owner, name) && getglobal(owner, name) isa Function && parentmodule(getglobal(owner, name)) === owner

"""Whether `qualifier` is a name `owner` binds to itself, as `IRVExtremism` in `IRVExtremism.f`."""
names_module(@nospecialize(qualifier::Any), owner::Module)::Bool = qualifier isa Symbol && isdefinedglobal(owner, qualifier) && getglobal(owner, qualifier) === owner

"""Whether callee `callee` names a function `owner` defines, bare (`f`) or qualified by `owner` (`Owner.f`)."""
own_callee(callee::Symbol, owner::Module)::Bool = own_function(callee, owner)
own_callee(callee::Expr, owner::Module)::Bool =
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
    return [
        Site("$(source.name) $(first(undocumented(statement).args).args[1])", source.path, marker.line, "computed by a function of $(nameof(owner)); define a function instead")
            for (marker, statement) in top_level_pairs(source)
            if marker isa LineNumberNode && is_constant(undocumented(statement)) &&
                calls_own_function(first(undocumented(statement).args).args[2], owner)
    ]
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
function forbidden_pattern_sites(repository::Repository, source::Source)::Vector{Site}
    return [
        Site("$(source.name) $(forbidden.name)", source.path, number, forbidden.message)
            for forbidden in repository.forbidden_patterns if source.name ∉ forbidden.skip_files
                for (number, line) in enumerate(split(source.text, '\n'))
                    if occursin(forbidden.pattern, line) && (isnothing(forbidden.unless) || !occursin(forbidden.unless, line))
    ]
end

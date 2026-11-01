# lint: non-public-access-begin  ExplicitImports keeps its per-use analysis internal
using ExplicitImports: ExplicitImports, improper_explicit_imports, improper_qualified_accesses
const USES = ExplicitImports.get_names_used
const MODULE_USES = ExplicitImports.filter_to_module
const QUALIFIED_USE = ExplicitImports.process_qualified_row
# lint: non-public-access-end

"""
    non_public_accesses(mod, file = entry_file(mod))

Each name of another module that `mod` reaches by qualified access (`Base.JuliaSyntax`) or explicit
import (`using Base: uniontypes`) though that module neither exports it nor declares it `public`.
ExplicitImports reads `file` and the files it includes. A qualified access has a site per use; an
explicit import has one per name, at its first import.
"""
function non_public_accesses(mod::Module, file::AbstractString = entry_file(mod))::Vector{Site}
    findings = improper_qualified_accesses(mod, file)
    accesses = unique(reduce(vcat, qualified_uses.(first.(findings), last.(findings), (USES(file),)); init = NamedTuple[]))
    imports = [row for (_, rows) in improper_explicit_imports(mod, file; strict = false) for row in rows if row.public_import === false]
    return [non_public_site.(accesses, getproperty.(accesses, :accessing_from)); non_public_site.(imports, getproperty.(imports, :importing_from))]
end

"""
Every qualified use in `submodule`, from the ExplicitImports file `analysis`, of a non-public name
that `findings` (ExplicitImports rows, one per name) report.
"""
function qualified_uses(submodule::Module, findings::AbstractVector{T}, analysis::Any)::Vector{NamedTuple} where {T <: NamedTuple}
    flagged = Set(access_key(row) for row in findings if !row.public_access && !row.self_qualified)
    resolved = QUALIFIED_USE.(filter(is_qualified, MODULE_USES(analysis, submodule).per_usage_info), (submodule,))
    found = filter(!isnothing, resolved)
    return found[in.(access_key.(found), (flagged,))]
end

"""Whether the ExplicitImports per-use row `use` is a qualified access (`Module.name`)."""
is_qualified(use::Any)::Bool = !isnothing(use.qualified_by)

"""The name of a qualified access `row` and the module it reaches the name in."""
access_key(row::NamedTuple)::Tuple{Symbol, Module} = (row.name, row.accessing_from)

"""The site of the ExplicitImports finding `row`, a name of the module `owner`, keyed `Owner.name`."""
function non_public_site(row::NamedTuple, owner::Union{Module, Symbol})::Site
    file, line, _ = rsplit(row.location, ':'; limit = 3)
    return Site("$owner.$(row.name)", String(file), parse(Int, line), "`$(row.name)` is not public in `$owner`")
end

"""The file `mod` was loaded from: its package entry file, or else the one source file its methods name."""
function entry_file(mod::Module)::String
    package_file = pathof(mod)
    if isnothing(package_file)
        return only(filter(isfile, unique(string(method.file) for method in defined_methods(mod))))
    end
    return package_file
end

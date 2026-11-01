using ExplicitImports: improper_explicit_imports, improper_qualified_accesses

"""
    non_public_accesses(mod, file = entry_file(mod))

Each name of another module that `mod` reaches by qualified access (`Base.JuliaSyntax`) or explicit
import (`using Base: uniontypes`) though that module neither exports it nor declares it `public`.
ExplicitImports reads `file` and the files it includes, and reports each name once, at its first use.
"""
function non_public_accesses(mod::Module, file::AbstractString = entry_file(mod))::Vector{Site}
    accesses = [row for (_, rows) in improper_qualified_accesses(mod, file) for row in rows if !row.public_access && !row.self_qualified]
    imports = [row for (_, rows) in improper_explicit_imports(mod, file; strict = false) for row in rows if row.public_import === false]
    return [non_public_site.(accesses, getproperty.(accesses, :accessing_from)); non_public_site.(imports, getproperty.(imports, :importing_from))]
end

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

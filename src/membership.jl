"""
The modules of a loaded package: its module, the loaded extensions `Base.get_extension` finds for it,
and every module nested in those. `belongs` decides membership for each reflection on a package.
"""
module Membership

export Package, belongs, module_bindings, package_bindings

"""A loaded package: `roots` holds its module and its loaded extension modules."""
struct Package
    roots::Vector{Module}
end

"""The `Package` of `mod`: `mod` and each loaded extension of it."""
Package(mod::Module)::Package = Package(Module[mod; extensions(mod)])

"""The loaded modules that `Base.get_extension` names as extensions of `mod`."""
extensions(mod::Module)::Vector{Module} = filter(Base.Fix1(extends, mod), collect(Module, values(Base.loaded_modules))) # lint: hidden-input  extensions load beside their parent

"""Whether `loaded` is the extension of `mod` that `Base.get_extension` finds by its name."""
extends(mod::Module, loaded::Module)::Bool = Base.get_extension(mod, nameof(loaded)) === loaded

"""Whether `candidate` belongs to `package`: its `parentmodule` chain reaches one of `package.roots`."""
function belongs(candidate::Module, package::Package)::Bool
    if candidate in package.roots
        return true
    end
    parent = parentmodule(candidate)
    if parent === candidate
        return false
    end
    return belongs(parent, package)
end

"""The values bound to the names of `mod`, unexported and compiler-made names included."""
module_bindings(mod::Module)::AbstractVector = getfield.((mod,), filter(Base.Fix1(isdefined, mod), names(mod; all = true)))

"""The `module_bindings` of every module of `package`: each root and the modules nested in it."""
package_bindings(package::Package)::AbstractVector = reduce(vcat, module_bindings.(package_modules(package)))

"""Each root of `package` and every module nested in one."""
package_modules(package::Package)::Vector{Module} = collect(Module, Iterators.flatten(nested_modules.(package.roots)))

"""`mod` and the modules bound in it whose parent it is, recursively."""
nested_modules(mod::Module)::Vector{Module} =
    Module[mod; collect(Module, Iterators.flatten(nested_modules.(child_modules(mod))))]

"""The modules bound in `mod` whose `parentmodule` is `mod`, `mod` itself excluded."""
child_modules(mod::Module)::Vector{Module} = filter(Base.Fix1(is_child, mod), module_bindings(mod))

"""Whether the binding `bound` is a module nested in `mod`."""
is_child(mod::Module, @nospecialize(bound::Any))::Bool = bound isa Module && bound !== mod && parentmodule(bound) === mod

end

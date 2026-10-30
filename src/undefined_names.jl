# A name a rename left pointing at nothing throws only when its testset runs, and
# the first failing testset aborts the suite, so one stale name hides every later
# one. Lowering resolves scopes without running anything.

"""
    import_names!(names, node)

Add the names a `using` or `import` statement binds to `names`.

`using Mod: a, b` binds `a` and `b`; `using Mod` binds whatever `Mod` exports, so
the module is loaded to ask it; `import Mod` binds `Mod` alone.
"""
function import_names!(names, node)
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    for clause in node.args
        if !(clause isa Expr)
            continue
        end
        if clause.head === :(:)
            for imported in clause.args[(begin + 1):end]
                if imported isa Expr && imported.head === :.
                    push!(names, last(imported.args))
                elseif imported isa Expr && imported.head === :as
                    push!(names, last(imported.args))
                end
            end
        elseif clause.head === :. &&
                length(clause.args) == 1 &&
                first(clause.args) isa Symbol
            module_name = first(clause.args)
            push!(names, module_name)
            loaded = try
                Core.eval(Main, :(import $module_name))
                getfield(Main, module_name)
            catch
                nothing
            end
            if loaded isa Module && node.head === :using
                union!(names, Base.names(loaded))
            end
        end
    end
    return names
end

"""The name a `struct`, `abstract type` or `module` declares, through `<:` and type parameters."""
function declared_name(declaration)::Symbol
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    while declaration isa Expr && declaration.head in (:curly, :(<:))
        declaration = first(declaration.args)
    end
    if declaration isa Symbol
        return declaration
    end
    return Symbol("")
end

"""
    bound_names!(names, node)

Add every name `node` binds anywhere to `names`: definitions, assignments,
destructuring and imports.

Over-approximated on purpose, so a reported name is one that nothing in reach
defines.
"""
function bound_names!(names, node)
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    if !(node isa Expr) || isempty(node.args)
        return names
    end
    target = first(node.args)
    # `f(x)::T = …` and `function f(x)::T` wrap the call in a return-type assertion.
    signature = target isa Expr && target.head === :(::) ? first(target.args) : target
    heads_a_call = node.head === :(=) && signature isa Expr && signature.head === :call
    if node.head === :function || node.head === :macro || heads_a_call
        if signature isa Expr &&
                signature.head === :call &&
                first(signature.args) isa Symbol
            push!(names, first(signature.args))
        end
    elseif node.head === :(=) && target isa Symbol
        push!(names, target)
    elseif node.head === :(=) && target isa Expr && target.head === :tuple
        for element in target.args
            if element isa Symbol
                push!(names, element)
            end
        end
    elseif node.head === :using || node.head === :import
        import_names!(names, node)
    elseif node.head in (:struct, :module) && length(node.args) >= 2
        push!(names, declared_name(node.args[2]))
    elseif node.head in (:abstract, :primitive)
        push!(names, declared_name(first(node.args)))
    end
    for child in node.args
        bound_names!(names, child)
    end
    return names
end

"""
    without_imports(node)

Return `node` with every `using` and `import` statement dropped.

`using` is a top-level form, so a body carrying one cannot sit in a `let`. The
names it binds are already in the defined set, so dropping it costs nothing.
"""
function without_imports(node)
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    if !(node isa Expr)
        return node
    end
    kept = Any[]
    for child in node.args
        if child isa Expr && (child.head === :using || child.head === :import)
            continue
        end
        push!(kept, without_imports(child))
    end
    return Expr(node.head, kept...)
end

"""
    included_path(argument, directory)

Resolve an `include` argument to a path, or `nothing` when it is not a literal.

Only a string, `@__DIR__` and `joinpath` of those resolve; any other expression is
never evaluated, because scanning a file must not run its code.
"""
function included_path(argument, directory::AbstractString)
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    pieces = path_pieces(argument, directory)
    if isnothing(pieces)
        return nothing
    end
    return joinpath(directory, pieces...)
end

"""The strings `argument` joins (`nothing` when any part is not a literal)."""
function path_pieces(argument, directory::AbstractString)
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    if argument isa String
        return [argument]
    end
    if argument isa Expr &&
            argument.head === :macrocall &&
            first(argument.args) === Symbol("@__DIR__")
        return [directory]
    end
    if argument isa Expr && argument.head === :call && first(argument.args) === :joinpath
        parts = [path_pieces(part, directory) for part in argument.args[(begin + 1):end]]
        if any(isnothing, parts)
            return nothing
        end
        return reduce(vcat, parts; init = String[])
    end
    return nothing
end

"""Add the names every file `node` includes by literal path binds to `names`, those files' includes too (`visited` stops cycles)."""
function follow_includes!(names, node, directory::AbstractString, visited = Set{String}())
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    if !(node isa Expr)
        return names
    end
    is_include = node.head === :call &&
        first(node.args) === :include &&
        length(node.args) == 2
    if is_include
        path = included_path(last(node.args), directory)
        if !isnothing(path) && isfile(path) && !(path in visited)
            push!(visited, path)
            included = Meta.parseall(read(path, String); filename = path)
            bound_names!(names, included)
            follow_includes!(names, included, dirname(path), visited)
        end
    end
    for child in node.args
        follow_includes!(names, child, directory, visited)
    end
    return names
end

"""
    module_globals!(names, value, scope)

Add every name lowered code resolves against `scope` to `names`.

Lowering resolves every local, so a name still reaching the module is either a
real global or nothing at all.
"""
function module_globals!(names, value, scope)
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    if value isa GlobalRef
        if value.mod === scope
            push!(names, value.name)
        end
        return names
    end
    statements = nothing
    if value isa Core.CodeInfo
        statements = value.code
    elseif value isa Expr
        statements = value.args
    end
    if isnothing(statements)
        return names
    end
    for statement in statements
        module_globals!(names, statement, scope)
    end
    return names
end

"""The `(line, node)` of every `@testset` under `node`, wherever a block, `let` or wrapper macro puts it; a testset's own body is not searched."""
function testset_nodes(node, line::Integer)::Vector{Tuple{Int, Any}}
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    found = Tuple{Int, Any}[]
    if !(node isa Expr)
        return found
    end
    if node.head === :macrocall && first(node.args) === Symbol("@testset")
        return [(line, node)]
    end
    for child in node.args
        if child isa LineNumberNode
            line = child.line
        else
            append!(found, testset_nodes(child, line))
        end
    end
    return found
end

"""
    undefined_names(path; scope)

Scan one test file for names its testsets use but nothing defines.

A name counts as defined when any binding of it appears anywhere in the file or its
literal includes (every scope, including modules and other testsets): the scan
over-approximates, so a reported name has no definition in reach.

Returns `(unresolved, unlowered)`. `unresolved` holds one `"line N: `name`"` entry
per undefined name. `unlowered` names the testsets whose macros could not be
expanded here, which the scan therefore did not cover: report it, because a scan
that quietly skips a testset reads exactly like one that cleared it.

`scope` is the module the testsets run in, which owns the macros the bodies use
and the names they resolve against. Pass `@__MODULE__`.
"""
function undefined_names(path; scope = Main)
    # lint: abstract-local  walks Julia ASTs, whose nodes are untyped
    directory = dirname(abspath(path))
    parsed = Meta.parseall(read(path, String); filename = path)
    defined = bound_names!(Set{Symbol}(), parsed)
    follow_includes!(defined, parsed, directory)

    unresolved = String[]
    unlowered = String[]
    for (line, target) in testset_nodes(parsed, 0)
        # The body, not the macrocall: a `@testset` that defers its body (ReTest)
        # lowers to bookkeeping the body never reaches, and the scan would clear
        # every file. A `let` gives the body the same local scope a testset does.
        lowered = try
            Meta.lower(scope, Expr(:let, Expr(:block), without_imports(last(target.args))))
        catch
            push!(unlowered, "line $line")
            continue
        end
        for name in sort!(collect(module_globals!(Set{Symbol}(), lowered, scope)))
            skip = occursin('#', String(name)) || name in defined || isdefined(scope, name)
            if !skip
                push!(unresolved, "line $line: `$name`")
            end
        end
    end
    return unresolved, unlowered
end

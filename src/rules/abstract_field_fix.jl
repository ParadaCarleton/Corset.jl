# The fixer of `abstract-field`: a struct with abstract-typed fields becomes a `@concrete struct`
# (ConcreteStructs.jl) and each such field `x::T` becomes `x <: T`, which the macro turns into a type
# parameter bounded by `T`. The fixer reads source text only, so it resolves a field's type name against
# the abstract types of Base and of the checked files, and leaves the rest to the rule.

const ANNOTATION_PARENTS = (SYNTAX.@K_str("::"), SYNTAX.@K_str("<:"), CURLY_KIND, SYNTAX.@K_str("braces"), SYNTAX.@K_str("where"), STRUCT_KIND, SYNTAX.@K_str("abstract"))
const FIELD_SETTERS = (:setfield!, :setproperty!, :modifyfield!, :modifyproperty!, :swapfield!, :swapproperty!, :replacefield!, :replaceproperty!, :setfieldonce!, :setpropertyonce!)

# Stands for a written field whose name the source does not spell out.
const DYNAMIC_FIELD = Symbol("<dynamic>")

"""Whether `name` is an abstract type Base exports; `Any` and `Type` stay out, since a field of either erases a type on purpose."""
is_base_abstract(name::Symbol)::Bool = name ∉ (:Any, :Type) && isdefined(Base, name) && getglobal(Base, name) isa Type && isabstracttype(getglobal(Base, name))

"""The abstract types Base exports, as a tuple so no caller can grow the shared set."""
const BASE_ABSTRACT_TYPES = Tuple(filter(is_base_abstract, names(Base)))

"""A field `name::annotation` of a struct, the `node` of the whole declaration."""
struct FieldDeclaration
    name::Symbol
    annotation::SYNTAX.SyntaxNode
    node::SYNTAX.SyntaxNode
end

"""
What the checked files do with structs, which decides the fields the fixer may touch: the abstract types
each module scope can name, the `written` field names (`DYNAMIC_FIELD` for a write that does not spell its field out), and
the struct names with a reference that adding a parameter could break or change (`escaping`): any use
other than a call `S(x)`, an annotation `::S` or a bound `<: S`.
"""
struct StructUsage
    abstract_types::Dict{String, Set{Symbol}}
    written::Set{Symbol}
    escaping::Set{Symbol}
end

"""Every node at or below `node` that `selected` accepts."""
function selected_nodes(selected::Function, node::SYNTAX.SyntaxNode)::Vector{SYNTAX.SyntaxNode}
    found = SYNTAX.SyntaxNode[]
    if selected(node)
        push!(found, node)
    end
    for child in node_children(node)
        append!(found, selected_nodes(selected, child))
    end
    return found
end

"""Whether syntax `node` is a `struct`, wrapped or not."""
is_struct(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) === STRUCT_KIND

"""Whether syntax `node` is a `struct` that no macro call wraps (`@kwdef` and `@concrete` rewrite what they wrap)."""
function is_plain_struct(node::SYNTAX.SyntaxNode)::Bool
    wrapped = false
    ancestor = node.parent
    while !isnothing(ancestor)
        wrapped |= SYNTAX.kind(ancestor) === SYNTAX.@K_str("macrocall")
        ancestor = ancestor.parent
    end
    return is_struct(node) && !wrapped
end

"""The name syntax of a declared type `head`: below `<:` and `curly`, as `struct_name` reaches it."""
function type_name_node(head::SYNTAX.SyntaxNode)::SYNTAX.SyntaxNode
    while SYNTAX.kind(head) in (CURLY_KIND, SUBTYPE_KIND)
        head = first(node_children(head))
    end
    return head
end

"""The `curly` syntax of the type a `struct` or `abstract type` node declares, or the bare name when it has no parameters."""
function declared_head(node::SYNTAX.SyntaxNode)::SYNTAX.SyntaxNode
    head = first(node_children(node))
    return SYNTAX.kind(head) === SUBTYPE_KIND ? first(node_children(head)) : head
end

"""The names of the type parameters the declared type `head` already has."""
function parameter_names(head::SYNTAX.SyntaxNode)::Vector{Symbol}
    if SYNTAX.kind(head) !== CURLY_KIND
        return Symbol[]
    end
    return Symbol[Symbol(SYNTAX.sourcetext(type_name_node(parameter))) for parameter in node_children(head)[2:end]]
end

"""Whether syntax `node` is an `abstract type` declaration."""
is_abstract_declaration(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) === SYNTAX.@K_str("abstract")

"""The key of the module scope that holds syntax `node` of `source`: its nearest `module`, or "" outside any (files included into one module share it)."""
function scope_key(source::Source, node::SYNTAX.SyntaxNode)::String
    ancestor = node.parent
    while !isnothing(ancestor) && SYNTAX.kind(ancestor) !== SYNTAX.@K_str("module")
        ancestor = ancestor.parent
    end
    return isnothing(ancestor) ? "" : "$(source.path):$(first(SYNTAX.byte_range(ancestor)))"
end

"""Whether syntax `node` is an `import` or `using` statement."""
is_import_statement(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) in (SYNTAX.@K_str("import"), SYNTAX.@K_str("using"))

"""
The abstract types a struct annotation can name, by module scope (`scope_key`): those of Base and those the scope
declares, less every name the scope also declares as a struct or imports (it may be a concrete type there).
A scope that declares nothing has only the abstract types of Base (`BASE_ABSTRACT_TYPES`).
"""
function abstract_types_by_scope(sources::AbstractVector{Source})::Dict{String, Set{Symbol}}
    declared = Dict{String, Set{Symbol}}()
    shadowed = Dict{String, Set{Symbol}}()
    for source in sources
        for node in selected_nodes(is_abstract_declaration, source.tree)
            union!(get!(declared, scope_key(source, node), Set{Symbol}()), Symbol[Symbol(SYNTAX.sourcetext(type_name_node(declared_head(node))))])
        end
        for node in selected_nodes(is_struct, source.tree)
            push!(get!(shadowed, scope_key(source, node), Set{Symbol}()), struct_name(node))
        end
        for node in selected_nodes(is_import_statement, source.tree)
            union!(get!(shadowed, scope_key(source, node), Set{Symbol}()), names_inside(node))
        end
    end
    resolvable = Dict{String, Set{Symbol}}()
    for key in union(keys(declared), keys(shadowed))
        resolvable[key] = setdiff(union(Set{Symbol}(BASE_ABSTRACT_TYPES), get(declared, key, Set{Symbol}())), get(shadowed, key, Set{Symbol}()))
    end
    return resolvable
end

"""The field names a write target `target` (the left side of an assignment) assigns: `x.f`, and each of a tuple's."""
function target_fields(target::SYNTAX.SyntaxNode)::Vector{Symbol}
    names = Symbol[]
    pending = SYNTAX.SyntaxNode[target]
    while !isempty(pending)
        current = pop!(pending)
        children = node_children(current)
        if SYNTAX.kind(current) === SYNTAX.@K_str(".") && length(children) == 2 && is_identifier_node(last(children))
            push!(names, Symbol(SYNTAX.sourcetext(last(children))))
        elseif SYNTAX.kind(current) === SYNTAX.@K_str("::")
            push!(pending, first(children))
        elseif SYNTAX.kind(current) === SYNTAX.@K_str("tuple")
            append!(pending, children)
        end
    end
    return names
end

"""Whether syntax `node` is an assignment or an update (`=`, `+=`), not a broadcast one (`.=`), which writes into the field's array."""
is_field_assignment(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) in (SYNTAX.@K_str("="), SYNTAX.@K_str("op="))

"""Whether syntax `node` calls one of `FIELD_SETTERS`: `setfield!(...)`, `Base.setfield!(...)`."""
function is_setter_call(node::SYNTAX.SyntaxNode)::Bool
    if !is_prefix_call(node)
        return false
    end
    callee = first(node_children(node))
    name = SYNTAX.kind(callee) === SYNTAX.@K_str(".") ? last(node_children(callee)) : callee
    return Symbol(SYNTAX.sourcetext(name)) in FIELD_SETTERS
end

"""Whether syntax `node` writes a field."""
is_field_write(node::SYNTAX.SyntaxNode)::Bool = is_field_assignment(node) || is_setter_call(node)

"""The field the setter call `call` writes: the quoted name, else `DYNAMIC_FIELD`."""
function setter_field(call::SYNTAX.SyntaxNode)::Symbol
    arguments = node_children(call)
    quoted = length(arguments) >= 3 && SYNTAX.kind(arguments[3]) === SYNTAX.@K_str("quote")
    return quoted ? Symbol(SYNTAX.sourcetext(first(node_children(arguments[3])))) : DYNAMIC_FIELD
end

"""Every field name the syntax `tree` writes: by assignment, or by a call of `FIELD_SETTERS`."""
function written_fields(tree::SYNTAX.SyntaxNode)::Vector{Symbol}
    names = Symbol[]
    for node in selected_nodes(is_field_write, tree)
        if is_field_assignment(node)
            append!(names, target_fields(first(node_children(node))))
        else
            push!(names, setter_field(node))
        end
    end
    return names
end

"""Whether the identifier `node` is a use that survives a new type parameter: a call `S(x)`, an annotation `::S` or a bound `<: S`."""
function is_kept_reference(node::SYNTAX.SyntaxNode)::Bool
    parent = something(node.parent)
    kept_call = is_prefix_call(parent) && node === first(node_children(parent))
    kept_type = SYNTAX.kind(parent) in (SYNTAX.@K_str("::"), SUBTYPE_KIND) && node === last(node_children(parent))
    return kept_call || kept_type
end

"""The identifier names `S` that `sources` use in a way `is_kept_reference` does not accept, other than where a struct is declared."""
function escaping_names(sources::AbstractVector{Source})::Set{Symbol}
    structs = Set{Symbol}()
    declared = Set{UInt}()
    for source in sources
        nodes = selected_nodes(is_struct, source.tree)
        union!(structs, struct_name.(nodes))
        union!(declared, objectid.(type_name_node.(declared_head.(nodes))))
    end
    escaping = Set{Symbol}()
    for source in sources
        for node in selected_nodes(is_identifier_node, source.tree)
            name = Symbol(SYNTAX.sourcetext(node))
            if name in structs && objectid(node) ∉ declared && !is_kept_reference(node)
                push!(escaping, name)
            end
        end
    end
    return escaping
end

"""The `StructUsage` of the parsed `sources`."""
function struct_usage(sources::AbstractVector{Source})::StructUsage
    written = Set{Symbol}()
    for source in sources
        union!(written, written_fields(source.tree))
    end
    return StructUsage(abstract_types_by_scope(sources), written, escaping_names(sources))
end

"""The statement `child` of a struct body, below its docstring."""
unwrapped_field(child::SYNTAX.SyntaxNode)::SYNTAX.SyntaxNode =
    SYNTAX.kind(child) === SYNTAX.@K_str("doc") ? unwrapped_field(last(node_children(child))) : child

"""Whether `child`, a statement of a struct body, is an annotated field: `@concrete` cannot express a `const` field, a default, a constructor or a macro."""
is_plain_field(child::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(unwrapped_field(child)) === SYNTAX.@K_str("::")

"""Whether `child`, a statement of a struct body, is a bare field `x`: the fixer cannot infer its type, so it stays bare."""
is_bare_field(child::SYNTAX.SyntaxNode)::Bool = is_identifier_node(unwrapped_field(child))

"""The `FieldDeclaration` of the annotated field `child` of a struct body."""
function field_declaration(child::SYNTAX.SyntaxNode)::FieldDeclaration
    node = unwrapped_field(child)
    name, annotation = node_children(node)
    return FieldDeclaration(Symbol(SYNTAX.sourcetext(name)), annotation, node)
end

"""Whether the annotation syntax `annotation` names an abstract type of `abstract_types`: bare, or applied to parameters, and not one of the struct's own `parameters`."""
function names_abstract_type(annotation::SYNTAX.SyntaxNode, abstract_types::AbstractSet{Symbol}, parameters::AbstractVector{Symbol})::Bool
    head = SYNTAX.kind(annotation) === CURLY_KIND ? first(node_children(annotation)) : annotation
    name = Symbol(SYNTAX.sourcetext(head))
    return SYNTAX.kind(head) === IDENTIFIER_KIND && name in abstract_types && name ∉ parameters
end

"""Whether syntax `node` is an identifier."""
is_identifier_node(node::SYNTAX.SyntaxNode)::Bool = SYNTAX.kind(node) === IDENTIFIER_KIND

"""The identifier names inside syntax `node`."""
names_inside(node::SYNTAX.SyntaxNode)::Set{Symbol} = Set{Symbol}(Symbol.(SYNTAX.sourcetext.(selected_nodes(is_identifier_node, node))))

"""
Whether `field`'s annotation names a type parameter that no field has as its whole type (`bare`). The macro
infers a parameter from the fields typed by it alone, so a parameter that only a bound mentions would need
explicit parameters at every construction.
"""
function needs_inference_from_bound(field::FieldDeclaration, parameters::AbstractVector{Symbol}, bare::AbstractSet{Symbol})::Bool
    return !issubset(intersect(names_inside(field.annotation), parameters), bare)
end

"""Whether assigning to `field` later could change the type its parameter was fixed at: a mutable struct's field that is written, or may be."""
function may_be_reassigned(name::Symbol, is_mutable::Bool, written::AbstractSet{Symbol})::Bool
    return is_mutable && (name in written || DYNAMIC_FIELD in written)
end

"""Whether `child`, a statement of a struct body, is a field the `@concrete` rewrite can keep: annotated or bare."""
is_expressible_field(child::SYNTAX.SyntaxNode)::Bool = is_plain_field(child) || is_bare_field(child)

"""Whether a bare field among `statements` of a struct is written later, which its new parameter would turn into a `convert` error."""
function retypes_bare_field(statements::AbstractVector{SYNTAX.SyntaxNode}, is_mutable::Bool, written::AbstractSet{Symbol})::Bool
    retypes = false
    for statement in filter(is_bare_field, statements)
        retypes |= may_be_reassigned(Symbol(SYNTAX.sourcetext(unwrapped_field(statement))), is_mutable, written)
    end
    return retypes
end

"""
The abstract-typed fields of struct syntax `node` the fixer makes parameters, in order. None when a
statement of the body is not a field (`x::T` or a bare `x`, which stays bare: the macro makes it an unbounded parameter
that the rule still flags), or when a reference to the struct could break or change
(`usage.escaping`). A field of a mutable struct that is
written anywhere keeps its type: the parameter would pin the type of the first value built, and a later
assignment of another type (a `Fill`, then a `Vector`) would throw.
"""
function parameter_fields(source::Source, node::SYNTAX.SyntaxNode, usage::StructUsage)::Vector{FieldDeclaration}
    statements = node_children(last(node_children(node)))
    is_mutable = startswith(SYNTAX.sourcetext(node), "mutable")
    if struct_name(node) in usage.escaping || !all(is_expressible_field, statements) || retypes_bare_field(statements, is_mutable, usage.written)
        return FieldDeclaration[]
    end
    parameters = parameter_names(declared_head(node))
    fields = field_declaration.(filter(is_plain_field, statements))
    bare = Set{Symbol}(Symbol.(SYNTAX.sourcetext.(getfield.(fields, :annotation))))
    abstract_types = get(usage.abstract_types, scope_key(source, node), Set{Symbol}(BASE_ABSTRACT_TYPES))
    chosen = FieldDeclaration[]
    for field in fields
        if names_abstract_type(field.annotation, abstract_types, parameters) && !may_be_reassigned(field.name, is_mutable, usage.written) && !needs_inference_from_bound(field, parameters, bare)
            push!(chosen, field)
        end
    end
    return chosen
end

const CONCRETE_PREFIX = "@concrete "

"""The repairs of struct syntax `node` in `source`: the `@concrete` prefix, and `x <: T` for each field `x::T` that becomes a parameter."""
function struct_repairs(source::Source, node::SYNTAX.SyntaxNode, usage::StructUsage)::Vector{Repair{ByteRewrite}}
    fields = parameter_fields(source, node, usage)
    if isempty(fields)
        return Repair{ByteRewrite}[]
    end
    start = first(SYNTAX.byte_range(node))
    edits = ByteRewrite[ByteRewrite(source.path, start:(start - 1), CONCRETE_PREFIX)]
    for field in fields
        push!(edits, ByteRewrite(source.path, SYNTAX.byte_range(field.node), "$(field.name) <: $(SYNTAX.sourcetext(field.annotation))"))
    end
    site = Site(string(struct_name(node)), source.path, first(SYNTAX.source_location(node)), "")
    return Repair.((site,), edits)
end

"""The repairs of the Julia file `source`."""
function abstract_field_repairs(source::Source, usage::StructUsage)::Vector{Repair{ByteRewrite}}
    repairs = Repair{ByteRewrite}[]
    for node in selected_nodes(is_plain_struct, source.tree)
        append!(repairs, struct_repairs(source, node, usage))
    end
    return repairs
end

const CONCRETE_STRUCTS = "ConcreteStructs" => "2569d6c7-a4a2-43d3-a901-331e8e4be471"

"""The text of the file `path` with the `edits` it owns made and `@concrete` imported into each module that gained a prefix."""
function concrete_file(edits::AbstractVector{ByteRewrite}, path::String)::Pair{String, String}
    text = read(path, String)
    own = edits[[edit.path for edit in edits] .== path]
    starts = [first(edit.range) for edit in own if edit.text == CONCRETE_PREFIX]
    root = SYNTAX.parseall(SYNTAX.SyntaxNode, text)
    scopes = import_scope.((root,), starts, (root,))
    imports = ByteRewrite[]
    for scope in unique(SYNTAX.byte_range, scopes)
        append!(imports, import_edit(path, text, scope, ["@concrete"], first(CONCRETE_STRUCTS)))
    end
    return path => rewritten(text, vcat(imports, own))
end

"""The new text of each file `edits` touch, as path => text, with ConcreteStructs added to the Project.toml above each."""
function concrete_texts(edits::AbstractVector{ByteRewrite})::Vector{Pair{String, String}}
    paths = unique(String[edit.path for edit in edits])
    return vcat(concrete_file.((edits,), paths), unique(first, Iterators.flatten(dependency_file.(paths, (CONCRETE_STRUCTS,)))))
end

"""
    abstract_field_plan(repository, directories)

An unsafe fix (`unsafe_fix_plan`): the rewrite changes the type of the struct, so a use the checked `directories`
do not show (another directory, a downstream package) can break or change silently, and a public constructor changes.
The `FixPlan` that writes the structs of `directories` with abstract-typed fields as `@concrete struct`s whose
such fields read `x <: T`, imports `@concrete` into each module and lists ConcreteStructs in the Project.toml
`[deps]`. A struct the macro cannot express, whose field a later write could retype, or that any checked file
refers to other than as `S(x)`, `::S` or `<: S`, stays (`parameter_fields`).
"""
function abstract_field_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(concrete_texts)}
    sources = directory_sources(repository, directories)
    usage = struct_usage(sources)
    return FixPlan(collect(Repair{ByteRewrite}, Iterators.flatten(abstract_field_repairs.(sources, (usage,)))), concrete_texts)
end

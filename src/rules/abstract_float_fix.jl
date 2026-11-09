# The fixer of `abstract-float`: each `AbstractFloat` the rule reports becomes `Real`. A method whose name is
# defined more than once in the file is left alone, because the rewrite could give two methods one signature.

"""The names of the methods defined at or below syntax `node`, one per definition."""
function definition_names(node::SYNTAX.SyntaxNode)::Vector{String}
    name = definition_name(node)
    inner = String[found for child in node_children(node) for found in definition_names(child)]
    return isempty(name) ? inner : vcat([name], inner)
end

"""The repairs of the Julia file `source`: one per reported `AbstractFloat` outside a method with siblings of its name."""
function abstract_float_repairs(source::Source)::Vector{Repair{ByteRewrite}}
    (; path, name, tree) = source
    definitions = definition_names(tree)
    repairs = Repair{ByteRewrite}[]
    for use in float_annotations(tree, false, false, "")
        if count(==(use.owner), definitions) <= 1
            push!(repairs, Repair(Site(name, path, first(SYNTAX.source_location(use.node)), ""), ByteRewrite(path, SYNTAX.byte_range(use.node), "Real")))
        end
    end
    return repairs
end

"""
    abstract_float_plan(repository, directories)

The `FixPlan` that writes each reported `AbstractFloat` as `Real`.
"""
abstract_float_plan(repository::Repository, directories::Tuple{Vararg{String}})::FixPlan{ByteRewrite, typeof(rewritten_texts)} =
    FixPlan(collect(Repair{ByteRewrite}, Iterators.flatten(abstract_float_repairs.(directory_sources(repository, directories)))), rewritten_texts)

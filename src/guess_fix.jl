# Heuristic result annotations for `--unsafe-fixes`. A guess needs no proof from inference, but
# inference vetoes it: a frame whose result the guess does not hold makes the site skipped.

"""A guessed result annotation: its `text`, the `kind` of heuristic, and whether inference `skipped` it."""
struct Guess
    text::String
    kind::String
    skipped::Bool
end

"""The names of the positional arguments of `definition`, `""` for one that is no plain identifier."""
function argument_names(definition::TypedDefinition)::Vector{String}
    names = String[]
    for written in node_children(definition.call)[2:end]
        argument = SYNTAX.kind(written) === SYNTAX.@K_str("::") ? first(node_children(written)) : written
        push!(names, SYNTAX.kind(argument) === IDENTIFIER_KIND ? SYNTAX.sourcetext(argument) : "")
    end
    return names
end

"""The last statement of the body of the definition `expression`, below any `return`."""
function final_statement(expression::Expr)::Any # lint: abstract-local  Expr nodes hold untyped arguments
    body = length(expression.args) >= 2 ? expression.args[2] : nothing
    while body isa Expr && body.head === :block && any(item -> !(item isa LineNumberNode), body.args)
        body = last(filter(item -> !(item isa LineNumberNode), body.args))
    end
    return body isa Expr && body.head === :return && !isempty(body.args) ? first(body.args) : body
end

"""Whether `statement` produces no value: `nothing`, or a loop."""
no_value(statement::Any)::Bool = statement === :nothing || (statement isa Expr && statement.head in (:for, :while))

"""The `Guess` for the number heuristic: the promotion of the argument types, or its `float` when only the result is non-integer."""
function number_guess(definition::TypedDefinition, names::AbstractVector{String})::Guess
    arguments = argument_types.(definition.frames)
    results = result_type.(definition.frames)
    if isempty(names) || any(isempty, names) || !all(types -> length(types) == length(names) && all(type -> type <: Number, types), arguments) || !all(type -> type <: Number, results)
        return Guess("", "", false)
    end
    integers = all(types -> all(type -> type <: Integer, types), arguments)
    floated = integers && !all(type -> type <: Integer, results)
    pieces = join(("typeof($name)" for name in names), ", ")
    promoted = length(names) == 1 ? "typeof($(only(names)))" : "promote_type($pieces)"
    expected(types::AbstractVector{Any})::Type = floated ? float(promote_type(types...)) : promote_type(types...)
    held = all(position -> results[position] <: expected(arguments[position]), eachindex(results))
    return Guess(floated ? "float($promoted)" : promoted, floated ? "number-float" : "number-promotion", !held)
end

"""The `Guess` for the unannotated result of `definition`, `kind == ""` when no heuristic applies."""
function guess_result(definition::TypedDefinition)::Guess
    expression = Expr(definition.node)
    name = SYNTAX.sourcetext(first(node_children(definition.call)))
    names = argument_names(definition)
    results = result_type.(definition.frames)
    statement = final_statement(expression)
    if occursin(r"^(is|has|can|should)_?[a-z]", name)
        return Guess("Bool", "predicate", !all(type -> type <: Bool, results))
    elseif no_value(statement)
        return Guess("Nothing", "nothing", !all(==(Nothing), results))
    elseif endswith(name, "!") && statement isa Symbol && string(statement) in names
        position = findfirst(==(string(statement)), names)
        arguments = argument_types.(definition.frames)
        held = all(index -> length(arguments[index]) >= position && results[index] == arguments[index][position], eachindex(results))
        return Guess("typeof($statement)", "bang", !held)
    end
    return number_guess(definition, names)
end

"""The `Guess` that widens the declared `Vector{E}` result of `definition` to `AbstractVector{E}`, `kind == ""` for any other declaration."""
function widen_guess(definition::TypedDefinition, scope::Module)::Guess
    annotation = return_annotation(Expr(definition.node))
    if !(annotation isa Expr && annotation.head === :curly && first(annotation.args) === :Vector)
        return Guess("", "", false)
    end
    text = "AbstractVector{" * join(string.(annotation.args[2:end]), ", ") * "}"
    held = try
        named = Core.eval(scope, Meta.parse(text))
        all(type -> type <: named, result_type.(definition.frames))
    catch
        false
    end
    return Guess(text, "vector-widening", !held)
end

"""
    guess_report(repository, directories, mod, frames)

Per heuristic kind, how many definitions the guesses cover and how many inference skips.
"""
function guess_report(repository::Repository, directories::Tuple{Vararg{String}}, mod::Module, frames::AbstractVector{Inferred})::Dict{String, Tuple{Int, Int}}
    by_place = frames_by_place(with_declared_frames(frames, mod))
    report = Dict{String, Tuple{Int, Int}}()
    for source in directory_sources(repository, directories), definition in typed_definitions(source, by_place)
        guess = declares_result(definition) ? widen_guess(definition, first(definition.frames).method.module) : guess_result(definition)
        if !isempty(guess.kind)
            covered, skipped = get(report, guess.kind, (0, 0))
            report[guess.kind] = guess.skipped ? (covered, skipped + 1) : (covered + 1, skipped)
        end
    end
    return report
end

"""
Code-quality rules checked on a loaded module and on its repository's Julia source. A rule is a
function returning the `Site`s it finds; `corset check` runs the rules and fails on them, and `offenders!`
reports one rule's. By default every site fails; a `Repository` given a baseline file holds each rule to
its per-rule counts there instead, failing on new offenders and lowering the counts when offenders go
away. The caller picks the rules, the module and source files they read, and their limits.
"""
module Corset

export Repository,
    Site,
    offenders!,
    @call_sites,
    @opt_sites,
    float64_ops,
    undefined_names

include("usage_error.jl")
include("ratchet.jl")
include("fix_plan.jl")
include("membership.jl")
include("entries.jl")
include("rules/general.jl")
include("rules/structs.jl")
include("rules/constants.jl")
include("rules/external_tools.jl")
include("entry_walk.jl")
include("candidates.jl")
include("rules/mutation.jl")
include("rules/dispatch.jl")
include("rules/float_widening.jl")
include("rules/jet.jl")
include("float64_scan.jl")
include("rules/imports.jl")
include("undefined_names.jl")
include("rules/where_return.jl")
include("rules/banned_names.jl")
include("rules/syntax_hazards.jl")
include("rules/concatenation_fix.jl")
include("rules/constant_array.jl")
include("rules/unwritten_undef.jl")
include("rules/abstract_float.jl")
include("rules/abstract_float_fix.jl")
include("rules/concrete_arg_fix.jl")
include("rules/non_public_access.jl")
include("rules/argument_types.jl")
include("registry.jl")
include("config.jl")
include("check.jl")
include("cli.jl")
include("precompile.jl")

end

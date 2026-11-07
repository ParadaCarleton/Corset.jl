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
include("rules.jl")
include("constants.jl")
include("external_tools.jl")
include("entry_walk.jl")
include("candidates.jl")
include("mutation.jl")
include("dispatch.jl")
include("float_widening.jl")
include("jet.jl")
include("float64_scan.jl")
include("imports.jl")
include("undefined_names.jl")
include("where_return.jl")
include("syntax_hazards.jl")
include("concatenation_fix.jl")
include("constant_array.jl")
include("concrete_arg_fix.jl")
include("typed_fix.jl")
include("guess_fix.jl")
include("non_public_access.jl")
include("registry.jl")
include("config.jl")
include("check.jl")
include("cli.jl")
include("precompile.jl")

end

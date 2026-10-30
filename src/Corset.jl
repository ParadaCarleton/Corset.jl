"""
Code-quality rules checked on a loaded module and on its repository's Julia source. A rule is a
function returning the `Site`s it finds; `ratchet!` fails a test on them. By default every site fails;
a `Repository` given a baseline file holds each rule to its per-rule counts there instead, failing on new
offenders and lowering the counts when offenders go away. The caller picks the rules, the module and
source files they read, and their limits.
"""
module Corset

export Repository,
    Site,
    ratchet!,
    offenders!,
    @call_sites,
    @opt_sites,
    float64_ops,
    undefined_names

include("ratchet.jl")
include("rules.jl")
include("jet.jl")
include("float64_scan.jl")
include("imports.jl")
include("undefined_names.jl")
include("where_return.jl")
include("registry.jl")
include("config.jl")
include("check.jl")
include("cli.jl")
include("precompile.jl")

end

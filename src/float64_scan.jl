# Counts Float64 operations in a call's fully optimized IR, a check for widening that a wrapper
# number type (one that throws on promotion to Float64) cannot see. See `float64_ops`.
using InteractiveUtils: code_llvm

const FLOAT64_IR_OPS =
    ("fadd", "fmul", "fsub", "fdiv", "frem", "fcmp", "fpext", "fptrunc", "call")

"""
    float64_ops(f, types)

Number of Float64 operations in the fully optimized IR of `f(::types...)`.

A wrapper number type observes a Float64 only when it is promoted with, or converted
from, a wrapped number, so a dependency that computes internally at Float64 and narrows
before returning is invisible to it — the expensive silent case, where the caller pays
Float64 arithmetic and keeps Float32 storage. The IR sees that widening whichever
package caused it, without forking or instrumenting the dependency.

Heuristic, not a proof: it reads the IR `optimize=true` produced for one concrete
signature, so a Float64 reached only through runtime dispatch is out of scope, and a
non-inlined callee is visible through its call signature rather than its body. Use
`== 0` on kernels that must stay narrow, and keep the positive controls so a change
to the filter cannot quietly disarm the check.
"""
function float64_ops(f::Any, types::Tuple)::Int
    buffer = IOBuffer()
    code_llvm(buffer, f, types; optimize = true, debuginfo = :none)
    return count(float64_line, split(String(take!(buffer)), '\n'))
end

"""Whether LLVM IR `line` is a `double` operation in `FLOAT64_IR_OPS`."""
float64_line(line::AbstractString)::Bool = occursin("double", line) && any(occursin.(FLOAT64_IR_OPS, line))

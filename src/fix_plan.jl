# A fixer proposes repairs; `apply_plan!` alone drops the opted-out ones and writes files.

"""One change a fixer proposes: the `site` it repairs, which a `# lint:` comment can pin, and the fixer's `edit`."""
struct Repair{E}
    site::Site
    edit::E
end

"""
A fixer's proposal: its `repairs`, and `rewrite`, a callable taking the edits of the repairs kept to the
new text of each file they touch (path => text).
"""
struct FixPlan{E, W}
    repairs::Vector{Repair{E}}
    rewrite::W
end

"""
    apply_plan!(plan, rule)

Write the files `plan` rewrites with the repairs no `# lint:` comment naming `rule` opts out, the filter
`judge` applies to findings. Every file is staged first (`write_all!`). Returns the sites repaired.
"""
function apply_plan!(plan::FixPlan{E}, rule::AbstractString)::Vector{Site} where {E}
    kept = plan.repairs[unopted_mask(Site[repair.site for repair in plan.repairs], rule)]
    rewrites::Vector{Pair{String, String}} = plan.rewrite(E[repair.edit for repair in kept])
    write_all!(first.(rewrites), last.(rewrites))
    return Site[repair.site for repair in kept]
end

"""
Write each of `texts` to the file of `paths` at its index, keeping the file's mode. Every text is
staged beside its file first, so a failure leaves all of `paths` as they were.
"""
function write_all!(paths::AbstractVector{String}, texts::AbstractVector{String})::Nothing
    staged::Vector{String} = tempname.(dirname.(paths); cleanup = false)
    try
        write.(staged, texts)
        chmod.(staged, filemode.(paths) .& 0o7777)
    catch
        rm.(filter(isfile, staged))
        rethrow()
    end
    mv.(staged, paths; force = true)
    return nothing
end

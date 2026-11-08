# JET reports as ratchet sites: each report is one site, keyed by the scope (the testset's
# analysis), the function it was found in and the report's kind, and placed at the source line of
# the frame where JET raised it, so the `jet` rule's opt-out comment on that line takes it out.
# Corset does not depend on JET: the macros use the JET the caller has loaded, so `corset` itself
# never pays for loading it.

const JET_ID = Base.PkgId(Base.UUID("c3a54625-cd67-489e-a8e7-0a5a0ff4e31b"), "JET")

"""The `JET` module among `modules` (the caller's loaded modules); throws when none is, naming the fix."""
function loaded_jet(modules::AbstractDict{Base.PkgId, Module} = Base.loaded_modules)::Module
    jet::Union{Nothing, Module} = get(modules, JET_ID, nothing)
    if isnothing(jet)
        throw(UsageError("`@call_sites` and `@opt_sites` use the caller's JET: add `using JET` before them"))
    end
    return jet
end

"""The `Site` of JET report `report`: its innermost frame names the function and the line."""
function jet_site(scope::String, report::Any)::Site # lint: unstable-variable  JET reports are duck-typed
    frame = last(report.vst)
    method = frame.linfo.def
    name = method isa Method ? method.name : :top_level
    return Site("$scope: $name $(nameof(typeof(report)))", string(frame.file), frame.line, "")
end

"""One site per report of JET analysis `result`."""
jet_sites(scope::String, result::Any)::Vector{Site} = jet_site.(scope, Base.invokelatest(loaded_jet().get_reports, result))

"""The code of `@call_sites` and `@opt_sites`: `sites` gains the sites of `report_macro` run on `arguments`."""
function jet_assertion(report_macro::Symbol, scope::String, source::LineNumberNode, sites::Symbol, arguments::Tuple)::Expr
    analysis = esc(Expr(:macrocall, GlobalRef(loaded_jet(), report_macro), source, arguments...))
    return :(append!($(esc(sites)), jet_sites($scope, $analysis)))
end

"""`@call_sites scope sites target_modules = (…,) call(…)`: `JET.@report_call`'s reports appended to the vector `sites`."""
macro call_sites(scope, sites, arguments...)
    return jet_assertion(Symbol("@report_call"), scope, __source__, sites, arguments)
end

"""`@opt_sites scope sites target_modules = (…,) call(…)`: `JET.@report_opt`'s reports appended to the vector `sites`."""
macro opt_sites(scope, sites, arguments...)
    return jet_assertion(Symbol("@report_opt"), scope, __source__, sites, arguments)
end

# The `jet` rule: `JET.report_call` on every frame the entry signatures compile, where the load path
# finds JET. It is not a dependency, so a run without it skips the rule and names it as skipped.

"""Whether the load path finds the package `id`; the `jet` rule runs only where it finds JET."""
installed(id::Base.PkgId)::Bool = !isnothing(Base.locate_package(id)) # lint: non-public-access  Base has no public way to ask the load path for a package

"""
    call_report_sites(repository, inferred, mod; comments = Dict())

One site per `JET.report_call` report on the frames `inferred` (as `audited_frames` keeps them under
`comments`) whose innermost frame is a method of `mod`'s package in `repository`'s files (JET's
`target_modules` scope, extensions and submodules included), keyed by method and report kind and
placed at that frame's line. A call that fails on only some branches of a union split counts: the
`Nothing` of a `findfirst` that nothing checks throws when it arrives. The same report reached from
several frames is one site. JET loads from the load path on first use.
"""
function call_report_sites( # lint: runtime-dispatch # lint: unstable-variable # lint: unmarked-mutation  JET loads at run time, reads only the frames' signature types, and its results are duck-typed
        repository::Repository, inferred::AbstractVector{Inferred}, mod::Module;
        comments::AbstractDict{String, Vector{OptOutComment}} = Dict{String, Vector{OptOutComment}}(),
    )::Vector{Site}
    jet = Base.require(JET_ID) # lint: non-public-access  JET is not a dependency, so it loads by its id
    package = Package(mod)
    sites = Site[]
    for item in audited_frames(repository, inferred, "jet", comments)
        result = Base.invokelatest(jet.report_call, item.code.parent.specTypes)
        for report in Base.invokelatest(jet.get_reports, result)
            append!(sites, call_report_site(repository, jet, report, package))
        end
    end
    return unique!(sites)
end

"""The site of JET report `report` when its innermost frame is a method of `package`; none otherwise."""
function call_report_site(repository::Repository, jet::Module, report::Any, package::Package)::Vector{Site} # lint: runtime-dispatch # lint: unstable-variable  JET reports are duck-typed
    frame = last(report.vst)
    method = frame.linfo.def
    if !(method isa Method && belongs(method.module, package) && in_repository(repository, method))
        return Site[]
    end
    key = "$(method_key(repository, method)) $(nameof(typeof(report)))"
    return [Site(key, string(frame.file), frame.line, report_message(jet, report))]
end

"""The first line of JET's message for `report`."""
function report_message(jet::Module, report::Any)::String # lint: runtime-dispatch  JET reports are duck-typed
    printed = IOBuffer()
    Base.invokelatest(jet.print_report_message, printed, report)
    return String(first(split(String(take!(printed)), '\n')))
end

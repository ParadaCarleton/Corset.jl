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
        error("`@call_sites` and `@opt_sites` use the caller's JET: add `using JET` before them")
    end
    return jet
end

"""The `Site` of JET report `report`: its innermost frame names the function and the line."""
function jet_site(scope::String, report::Any)::Site # lint: abstract-local  JET reports are duck-typed
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

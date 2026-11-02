# Compiles the `check` path while Corset precompiles, so a run of `corset` reuses the cached code
# and spends its time and memory on the project, not on the compiler.
# COV_EXCL_START
# The workload runs while the package precompiles, outside any test.

# fatou-ignore unused-import: the macro expansion names the module
using PrecompileTools: PrecompileTools, @compile_workload

"""A package for the precompile workload to check: it holds one finding for a module rule to report."""
module WorkloadPackage
    const COUNTER = Ref(0)
    bump(x) = x + COUNTER[]
    struct Holder
        held::Any
    end
end

@compile_workload begin
    root = mktempdir()
    try
        mkpath(joinpath(root, "src"))
        write(joinpath(root, "Project.toml"), "name = \"WorkloadPackage\"\n")
        write(
            joinpath(root, "src", "WorkloadPackage.jl"),
            "module WorkloadPackage\nconst COUNTER = Ref(0)\nbump(x) = x + COUNTER[]\nstruct Holder\n    held::Any\nend\nend\n",
        )
        config = with_overrides(load_config(root), true, ["fatou" => :allow, "jscpd" => :allow], nothing)
        WorkloadPackage.bump(1)
        sources = seed_sources(config, root, nothing, WorkloadPackage, devnull)
        frames = seeded_frames(sources, WorkloadPackage)
        seed_summary(sources, frames, 0)
        findings, _ = run_rules(config, root; mod = WorkloadPackage, signatures = frames)
        for format in ("human", "concise")
            print_findings(devnull, root, findings, format)
        end
        print_rules(devnull, config)
        exit_code(findings, false)
        redirect_stderr(devnull) do
            redirect_stdout(devnull) do
                main(["rules", root])
                main(["check", root, "--no-load", "--pedantic", "--allow", "fatou", "--allow", "jscpd"])
            end
        end
    finally
        rm(root; recursive = true, force = true)
    end
end
# COV_EXCL_STOP

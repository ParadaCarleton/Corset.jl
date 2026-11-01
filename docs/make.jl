using Documenter, Corset

DocMeta.setdocmeta!(Corset, :DocTestSetup, :(using Corset); recursive = true)

makedocs(;
    sitename = "Corset.jl",
    authors = "Carlos Parada",
    modules = [Corset],
    checkdocs_ignored_modules = [Corset.WorkloadPackage],
    format = Documenter.HTML(canonical = "https://paradacarleton.github.io/Corset.jl/stable"),
    pages = [
        "Home" => "index.md", "Guide" => "guide.md", "CLI" => "cli.md", "Rules" => "rules.md", "API" => "api.md",
        "Internals" => ["Source rules" => "internals/source.md", "Typed-code rules" => "internals/typed.md", "Runner" => "internals/runner.md"],
    ],
    warnonly = false,
)

deploydocs(repo = "github.com/ParadaCarleton/Corset.jl.git", push_preview = true)

using Documenter, Corset

DocMeta.setdocmeta!(Corset, :DocTestSetup, :(using Corset); recursive = true)

makedocs(;
    sitename = "Corset.jl",
    authors = "Carlos Parada",
    modules = [Corset],
    checkdocs_ignored_modules = [Corset.WorkloadPackage],
    format = Documenter.HTML(canonical = "https://paradacarleton.github.io/Corset.jl/stable", size_threshold_warn = 200 * 1024, size_threshold = 400 * 1024),
    pages = ["Home" => "index.md", "Guide" => "guide.md", "CLI" => "cli.md", "Rules" => "rules.md", "API" => "api.md"],
    warnonly = false,
)

deploydocs(repo = "github.com/ParadaCarleton/Corset.jl.git", push_preview = true)

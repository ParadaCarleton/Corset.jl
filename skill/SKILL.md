---
name: corset
description: Run Corset, the Julia code-quality checker, on a package; read its findings, apply its fixers and fix the code. Use when a Julia package has a Corset config or baseline, when CI fails on `corset check`, or when asked to lint or clean up Julia code.
---

# Corset

Corset checks Julia packages with the compiler's answers (inferred types, closures, globals) and with source rules.

## Run

- Run `corset check .` in the package root. The package must load.
- Run `corset rules` for every rule, its group and its level.
- Add `--pedantic` for house-style rules. Add `--format concise` for short output.
- Without the `corset` executable run: `julia --project=. -e 'using Corset; exit(Corset.main(ARGS))' -- check .`
- Read the rule list and the fix of each rule in `docs/src/rules.md` of the Corset repository. Do not copy it into notes.

## Read a finding

- A finding names a rule, a file, lines and a detail. The detail states the fix.
- Fix the code so the rule holds. Do not change the code to dodge the rule's check.
- A baseline file lists allowed offenders. Run `corset baseline` only to lower it.

## Fix

- Run `corset check --diff` to preview the fixes. Run `corset check --fix` to write them.
- Review every diff. Run the package tests after each fix.
- A fixer in the unsafe tier (`--unsafe-fixes`, when `corset check --help` lists it) guesses types or storage. Use it only after you review its diff.
- A rule without a fixer needs a manual edit.

## Waivers

- Syntax: `# lint: RULE reason`. Also `RULE-begin` and `RULE-end` for a block, and `RULE-file` for a file.
- A waiver needs human approval. Never add one, a baseline entry, or a lowered rule level on your own.
- If a rule seems wrong, stop and ask the user. Give the rule name, the site and your reason.

## Do not

- Never game a rule. Example: `similar(Vector{T}, n)` replaces `Vector{T}(undef, n)` and keeps its defect. Use `similar(x, T, n)` with an array `x` whose storage the result must follow.
- Never raise a baseline count: no `corset baseline` after new findings.
- Never delete a test or loosen a type annotation to silence a finding.
- Never rewrite findings in files you did not touch, unless asked.

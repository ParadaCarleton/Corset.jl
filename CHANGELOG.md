# Changelog

## 0.4.0

- Breaking: the rule `unwritten-undef` replaces `nan-initializer`. Rename `nan-initializer` in `[preferences.Corset.levels]`, `--allow`, `--warn`, `--deny` and `# lint:` comments.
- `unwritten-undef` also reports `similar(…)` and `T(undef, …)` arrays not provably written in full before any read.

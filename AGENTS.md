# Repository Guidelines

## Project Structure & Module Organization
- Source code lives under `src/`, namespaced `MyProjects.<Area>.<Subarea>` (e.g., `src/MyProjects/Topology/C/EnrichedTopCat.lean`).
- Build configuration: `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`.
- Dependencies are pinned via mathlib in `lakefile.lean` (v4.23.0-rc2).
- There is no dedicated test suite; compilation is the primary check. Place quick sanity `example` blocks near new lemmas.

## Build, Test, and Development Commands
- Build everything: `lake build`
- Build a module (preferred over file globs):
  - `lake build MyProjects.Topology.C.EnrichedTopCat`
  - `lake build MyProjects.Topology.C.FundamentalGroupScaffold`
- Run the default executable: `lake exe myexe` (root `MyProjects.Main`).
- Update deps (rare): `lake update` (keep versions pinned unless coordinated).

## Coding Style & Naming Conventions
- Lean style, 2-space indent, UTF-8, LF line endings.
- File/module names use PascalCase; namespaces mirror paths (e.g., `namespace MyProjects.Topology.C.Uniform`).
- Start modules with `noncomputable section`; use `open scoped Topology` and only necessary `open` statements.
- Prefer constructive proofs over `axiom`. If a placeholder is unavoidable, mark with a clear TODO and keep the surface API stable.
- Lemma names follow mathlib conventions: `..._apply`, `..._comp`, `..._fst/snd`, with `@[simp]` where appropriate.

## Testing Guidelines
- Treat a clean `lake build` as required. Add small `example`/`@[simp]` checks alongside new APIs to exercise usage.
- For larger changes, add a minimal demo in a sibling file under the same directory (kept out of public APIs).

## Commit & Pull Request Guidelines
- Commits: imperative present, concise scope, e.g., `topology/c: add curry/uncurry simp lemmas`.
- PRs: include a brief summary, list affected modules, rationale, and before/after snippets. Link issues when applicable.
- Requirements: `lake build` passes; no unrelated diffs; docs updated when APIs change.

## Agent-Specific Instructions
- Keep patches minimal and localized; don’t modify dependency pins or license files.
- Use module targets (not file globs) when building. Avoid networked changes and escalated commands.
- Follow this AGENTS.md for any files within its directory tree.


# Repository Guidelines

## Project Structure & Module Organization
- Source lives under `src/`, namespaced `MyProjects.<Area>.<Subarea>`.
  Example: `src/MyProjects/Topology/C/EnrichedTopCat.lean` with `namespace MyProjects.Topology.C`.
- Build config at repo root: `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`.
- Dependencies are pinned via mathlib in `lakefile.lean` (v4.23.0-rc2). Do not change pins without coordination.

## Build, Test, and Development Commands
- Build everything: `lake build` — compiles all modules.
- Build a module (faster): `lake build MyProjects.Topology.C.EnrichedTopCat`.
- Run default executable: `lake exe myexe` (entry `MyProjects.Main`).
- Update deps (rare): `lake update` — keep versions pinned unless planned.

## Coding Style & Naming Conventions
- Lean style: 2‑space indent, UTF‑8, LF line endings; PascalCase file/module names.
- Start modules with `noncomputable section`; use `open scoped Topology` and only necessary `open` statements.
- Namespaces mirror paths (e.g., `namespace MyProjects.Topology.C.Uniform`).
- Prefer constructive proofs; avoid `axiom`. If a placeholder is unavoidable, add a clear TODO and keep the public API stable.
- Lemma naming follows mathlib (`…_apply`, `…_comp`, `…_fst`/`…_snd`); use `@[simp]` where appropriate.

## Testing Guidelines
- There is no dedicated test suite; a clean `lake build` is required.
- Add small `example` blocks near new lemmas and simple `@[simp]` checks to exercise usage.
- For larger changes, add a minimal demo in a sibling file under the same directory (kept out of public APIs).

## Commit & Pull Request Guidelines
- Commits: imperative present, concise scope. Example: `topology/c: add curry/uncurry simp lemmas`.
- PRs: brief summary, affected modules, rationale, before/after snippets; link issues when applicable.
- Requirements: `lake build` passes; no unrelated diffs; docs updated when APIs change.

## Agent‑Specific Instructions
- Keep patches minimal and localized; don’t modify dependency pins or license files.
- Use module targets (not file globs) when building.
- Avoid networked changes and escalations; follow this AGENTS.md for the entire tree.


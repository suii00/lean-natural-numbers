# AGENTS.md (Codex)

> **Motto**: "Small, clear, safe steps — always grounded in real docs."

## Principles
- Keep changes **minimal**, **safe**, and **reversible**.
- Prefer **clarity** over cleverness; **simplicity** over complexity.

## Knowledge & Libraries
- **Before coding, use the Search and Read features to confirm the latest mathlib APIs.**
- If uncertain, **pause and request clarification**.

## Workflow
1. **Plan**: Share a short plan before major edits; prefer small, reviewable diffs.
2. **Read**: Identify and read all relevant files **before** changing anything.
3. **Verify**: Re-check external APIs/assumptions against docs; after edits, re-read affected code for invariants.
4. **Implement**: Keep scope tight; single-purpose modules/functions.
5. **Test & Docs**: Add at least one test and update docs with each change; align assertions with current logic.
6. **Reflect**: Address root causes; consider adjacent risks to prevent regressions.

## Code Style & Limits (Lean/mathlib)
- **`sorry` and `trivial` are last resorts**; keep usage to a **minimum**.
- If `sorry`/`trivial` must be committed, **always add a `TODO:` comment** explaining **why** and **what follow-up** is planned; usage must be **justifiable**.
- Prefer small, reusable lemmas; use meaningful **snake_case** names.
- Prefer short proofs; use **term-style** when obvious; if tactics get long, extract helper lemmas.
- Use `@[simp]` / `@[norm_cast]` only when they reduce proof noise; include a brief rationale.
- Put a module-level **docstring** at the top (overview, key defs/lemmas, small example).

## Collaboration & Accountability
- Escalate when requirements are ambiguous, security-sensitive, or when UX/API contracts would change.
- Ask early if confidence is **< 80%**.
- Scoring guideline: **−4** for wrong/breaking changes, **+1** for successful changes, **0** for honest uncertainty.
- Prioritize **correctness** over speed.
- **Before introducing a potentially breaking change**, ask for confirmation and obtain approval; briefly note a rollback plan.

## Language & Communication
- **Document language**: English.
- **Responses & development memos**: Japanese.

## Commit Messages (Conventional Commits)
- **Types**: `feat`, `fix`, `docs`, `refactor`, `test`, `ci`, `perf`, `build`, `chore`, `revert`.
- **Subject**: English, imperative mood, ≤ 72 chars.
- **Body**: Japanese allowed (context, intent, alternatives, trade-offs, related PR/Issue, `TODO` details).
- **Breaking changes**: mark with **`type!:`** *and* a **`BREAKING CHANGE:`** footer; require prior approval and include a rollback note.
- Cross‑reference issues/PRs; include follow‑ups for any `sorry`/`trivial`.

### Scopes (initial set)
`algebra`, `analysis`, `topology`, `order`, `number_theory`, `data`, `tactic`, `measure`

## Testing Minimum (Lean)
- All changes **compile** (`lake build`).
- Add at least one **`example` or small lemma test** relevant to the change.
- Update the **module docstring** for any public `def`/`lemma` changes.

## Toolchain & Updates (Lean/mathlib)
- **Policy**: Track the **latest stable Lean 4** and **latest mathlib** (rolling).
- **Cadence**: **Weekly bump** (e.g., every Monday JST).
- **Process**:
  1) `lake update` → `lake build` → run tests/examples  
  2) open a PR with `build(deps): bump Lean/mathlib`  
  3) if breakages occur, either fix promptly or **rollback the same day**  
- **Rollback**: revert the bump commit if builds/tests fail or regress; include a short explanation and open a follow‑up issue if needed.
- **Upstream breaking**: treat as potentially breaking; ask for approval and note a rollback plan in the PR body.

## CI Policy (Standard)
- **Build**: run `lake build` to ensure the code compiles.
- **Lint**: enforce Conventional Commits via **commitlint** (subject in English, ≤ 72 chars).
- **Policy**: detect any use of `sorry`/`trivial`; **fail** if the same commit doesn’t include a `TODO:` with rationale and follow‑up.
- **Release hygiene (on merges to `main`, optional)**: generate/update **CHANGELOG** from commit history.

## Release & Versioning
- **Cadence**: **Weekly tags** after `main` is stable. Tag as **`vX.Y.Z`** (SemVer).
- **Changelog**: Auto‑generate release notes from Conventional Commits.
- **Version bumps**:
  - `BREAKING CHANGE` or `type!:` → **MAJOR**
  - `feat` → **MINOR**
  - `fix` (and similar bug‑fix level) → **PATCH**
- **Gate**: Tag only when CI is green and no pending high‑risk issues remain.
- **Owner**: Maintainer triggers tagging (or CI job) after quick sanity review.
- **Rollback**: If post‑tag regressions appear, create a hotfix (`fix:`) and retag with the next PATCH.

## Security Posture (math‑only)
- Work only with **public, non‑PII mathematical assets**; no sensitive personal data expected.
- For any **external datasets or snippets**, include **license/attribution** clearly.
- If any **secret/PII/unintended sensitive field** is detected, **remove immediately** in a follow‑up commit and add a short **prevention note** (what happened / how to avoid next time).

## Ownership & Review
- **PRs to `main` require 1 human reviewer** (no self‑merge without review).
- **Self‑merge** allowed only after **24h cooldown** and **green CI**.
- For potentially breaking changes, prior **approval is mandatory** and a rollback note must be included.

## Quick Checklist
- **Plan → Read files → Verify docs (mathlib: Search/Read) → Implement → Test + Docs → Reflect**
- **No `sorry`/`trivial` without `TODO`** (reason + follow‑up)
- **Potentially breaking? Ask first**; include a rollback note
- **PR to `main` needs 1 reviewer**; self‑merge only with 24h cooldown + green CI

# Phase 1 Outstanding Tasks

## Optional Stopping Proof
- **Location:** `src/MyProjects/ST/Phase1_Simplified.lean:224`
- **Status:** `Martingaleℝ.stopped_is_martingale_bounded` currently depends on a `TODO` (sorried proof) for the martingale property after stopping.
- **Next Steps:** Reuse Mathlib's stopped-process lemmas (`MeasureTheory.martingale_stoppedProcess`, sub/supermartingale variants) to discharge the goal. Confirm the required super/submartingale instances and document the finite-measure assumption.

## Examples and Regression Checks
- **Goal:** Enrich Phase 1 with a handful of concrete martingale / optional stopping examples (constant, simple random walk truncations, etc.) and small lemmas that double as tests.
- **Scope:** Aim for 5–10 examples spread across `Phase1_Simplified.lean` or a companion file so that future refactors have reference cases.

## Lint and Warning Cleanup
- **`simp` arguments:** Replace lingering `simpa` calls (lines ~91, 94, 105) with `simp` or adjust argument lists to avoid the `min_le_iff` warning.
- **Unused variables:** Address section-level unused variables (e.g., `m`, `n` around line 124 and `[MeasureSpace Ω]` in `stoppedProcess_neg`). Use `variable` scoping or `omit` blocks per file guidelines.
- **Goal:** Keep Phase 1 warning-free to simplify future diffs and CI runs.

## Documentation Touch-ups
- Cross-link the new Phase 1 martingale definitions with later phases (Phase1_PRAGMATIC, Step3_Measurability) so readers know which file to extend.
- Mention the outstanding optional-stopping proof and testing plan in the Phase 1 overview prose so contributors have immediate guidance.

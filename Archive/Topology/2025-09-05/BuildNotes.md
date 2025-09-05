今回遭遇したエラーと対処方法をまとめてmdファイルを作成してください。


作業ログをまとめた Markdown を追加します。以下の内容で新規ファイルを作成してください。

ファイルパス: BUILD_NOTES_TopologyB.md

内容:

TopologyB_Bourbaki — Build Notes (Errors and Fixes)
This document summarizes the main errors encountered while re‑implementing Section B (path lifting for covering maps) in an ext; simp oriented style, and the concrete fixes applied to keep the build green at each step.

The overall design follows Option A (no sheet, only sheetMap + bundled β) and Option 2 (Phase 6 added via apply‑level lemmas first, then lifted to Path‑level by ext; simp).

Instance definality on products ({x // x ∈ d.U} × d.I)
Symptom:
“synthesized type class instance is not definitionally equal … instTopologicalSpaceProd … this vs … d.instTopI”
“failed to synthesize TopologicalSpace ({ x // x ∈ d.U } × d.I)”
Root cause: Mixing d.e (Homeomorph) with product topologies built from a locally synthesized TopologicalSpace d.I vs d.instTopI.
Fixes:
No global instances for d.I.
Use local letI/haveI: letI : TopologicalSpace d.I := d.instTopI in the smallest scope.
Prefer set‑level β using d.e or d.e.toEquiv; bundle continuity separately.
Implement sheetMap under a local letI and prove bundled β @[simp] sheet_comp_eq_inclB by set‑level rewriting.
sheet/sheet_base vs sheetMap
Symptom: Instance clashes around sheet (u ↦ d.e.toEquiv.symm (u,i)).
Fixes:
Keep sheet/sheet_base commented (Option A).
Use only sheetMap (bundled) + local letI.
Add sheetMap_through via d.e.left_inv and d.e.injective.
Path .map and evaluation
Normalize: Always (γ.map (f := p) h.continuous).
Add [simp] path_map_apply: (γ.map …) t = p (γ t).
Use ContinuousMap.comp_apply in simp.
Path endpoints — “simp made no progress” / True artifacts
Symptom: simp produces True instead of the target equality (e.g., γ (cov.pts 0) = b₀).
Fixes:
Use theorem forms:
[simp] path_source_I0 (γ) : γ I0 = source as by simpa [I0] using γ.source
[simp] path_target_I1 (γ) : γ I1 = target as by simpa [I1] using γ.target
Build the equality then rewrite:
have h0' : γ (cov.pts 0) = b₀ := by simpa [cov.start] using path_source_I0 (γ := γ)
have h0 : b₀ = γ (cov.pts 0) := h0'.symm
simpa [h0] using (Path.refl b₀).target
“Function expected at γ” / dependent argument ordering
Symptom: γ a appears in the type of an earlier argument.
Fix: Reorder arguments so γ and a precede d : EvenlyCoveredAt p (γ a)
liftPathLocalOn (h) (γ) (a b) (d : EvenlyCoveredAt p (γ a)) …
γab related errors
Avoid named γab := … in simpa; inline the definition or use a direct construction.
liftPathLocal startpoint equality without sheet
Use sheetMap_through at the starting point, rewrite subtype inputs to match, unfold liftAlong once.
Two‑interval gluing
Midpoint equality via apply‑level β:
congrArg (fun δ => δ I1) (liftPathLocal_map_apply … I1)
simp with path_map_apply and subpath.
PathCover fold — dependent recursion
Symptoms:
Unknown identifier build, assumption fails, True artifacts.
Nat lemma shape mismatches (Nat.le_of_lt_succ used in wrong direction).
Fixes:
Keep fold bodies commented for now (Option 2).
Introduce coverConcatCore (left fold nucleus):
(k : Fin (cov.n+1)) → Path b₀ (γ (cov.pts k))
Base: Path.refl b₀ with endpoint rewritten via γ.source and cov.start
Step: explicit i : Fin cov.n := ⟨k, hklt⟩, prev.trans (subpath …)
Next:
Add coverConcatCore_apply (t) (apply‑level fold)
Define coverConcat := coverConcatCore … ⟨cov.n, by simp⟩ and prove Path equality by ext t; simp [coverConcatCore_apply]
Implement liftPathOnCover as strong recursion with state (e_k, Γ_k, p e_k = γ (pts k)) and fold the apply‑level β.
TopCat morphism .continuous
Fix: Use ContinuousMap.continuous f explicitly.
Comment hygiene
Remove stray /- before namespace CoveringMap; mark deferred blocks with balanced comment pairs and NOTE tags.
ext; simp discipline
Normalize simp lists: include ContinuousMap.comp_apply, path_map_apply.
Prefer apply‑level β lemmas, then upgrade to Path equality by ext t; simp.
Keep Path [simp] lemmas small and stable.
Stable API choices
sheetMap + @[simp] sheet_comp_eq_inclB
liftAlong + @[simp] liftAlong_beta
liftPathLocal, liftPathLocalOn (+ …_map_apply), liftPathTwo
PathCover fold via coverConcatCore → coverConcat → liftPathOnCover with apply‑level β
Practical tips
Subtype rewrites: Subtype.ext, ext; rfl for Fin
Nat conversions:
Nat.succ_lt_succ_iff.mp : a+1 < b+1 → a < b
Nat.lt_succ_of_le : a ≤ b → a < b+1
Nat.le_of_lt_succ : a < b+1 → a ≤ b
Endpoint: Use γ.source/γ.target theorem forms to avoid True artifacts.
This blueprint keeps the build green while we layer in Phase 6. When ready, add coverConcatCore_apply (t) and then replace coverConcat with coverConcatCore … ⟨cov.n, by simp⟩, followed by liftPathOnCover as a strong recursion with apply‑level β; Path equalities then follow by ext t; simp.

（この Markdown は手元のファイルに追加してください。リポジトリのルート BUILD_NOTES_TopologyB.md がおすすめです。）


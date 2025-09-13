import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# 蛇の補題とホモロジーの長完全列

Bourbakiの精神：完全系列を射の核・像の包含関係として読む。
連結準同型は「境界を追跡する射」として自然に現れる。
-/

namespace SnakeLemma

open Function

universe u

variable {R : Type u} [CommRing R]

/-- 可換図式の設定：
```
  0 → A₁ -f₁→ B₁ -g₁→ C₁ → 0
      ↓α     ↓β     ↓γ
  0 → A₂ -f₂→ B₂ -g₂→ C₂ → 0
```
-/
structure SnakeDiagram
  (A₁ B₁ C₁ A₂ B₂ C₂ : Type u)
  [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]
  [AddCommGroup A₂] [AddCommGroup B₂] [AddCommGroup C₂]
  [Module R A₁] [Module R B₁] [Module R C₁]
  [Module R A₂] [Module R B₂] [Module R C₂] where
  -- 水平射（短完全列）
  f₁ : A₁ →ₗ[R] B₁
  g₁ : B₁ →ₗ[R] C₁
  f₂ : A₂ →ₗ[R] B₂
  g₂ : B₂ →ₗ[R] C₂
  -- 垂直射
  α : A₁ →ₗ[R] A₂
  β : B₁ →ₗ[R] B₂
  γ : C₁ →ₗ[R] C₂
  -- 短完全性
  exact₁ : LinearMap.range f₁ = LinearMap.ker g₁
  exact₂ : LinearMap.range f₂ = LinearMap.ker g₂
  f₁_inj : Function.Injective f₁
  f₂_inj : Function.Injective f₂
  g₁_surj : Function.Surjective g₁
  g₂_surj : Function.Surjective g₂
  -- 可換性
  comm₁ : β.comp f₁ = f₂.comp α
  comm₂ : γ.comp g₁ = g₂.comp β

namespace SnakeDiagram

variable {A₁ B₁ C₁ A₂ B₂ C₂ : Type u}
variable [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]
variable [AddCommGroup A₂] [AddCommGroup B₂] [AddCommGroup C₂]
variable [Module R A₁] [Module R B₁] [Module R C₁]
variable [Module R A₂] [Module R B₂] [Module R C₂]
variable {D : SnakeDiagram (R:=R) A₁ B₁ C₁ A₂ B₂ C₂}

/-- 連結準同型 `δ : ker γ → coker α` の構成。
Mathlib の `SnakeLemma.δ'`（Module 版）を核／余核に特化して与える。 -/
noncomputable def connecting_homomorphism
    (D : SnakeDiagram (R:=R) A₁ B₁ C₁ A₂ B₂ C₂) :
  LinearMap.ker D.γ →ₗ[R] (A₂ ⧸ LinearMap.range D.α) := by
  classical
  -- 記号の短縮
  let i₁ : A₁ →ₗ[R] A₂ := D.α
  let i₂ : B₁ →ₗ[R] B₂ := D.β
  let i₃ : C₁ →ₗ[R] C₂ := D.γ
  let f₁ : A₁ →ₗ[R] B₁ := D.f₁
  let f₂ : B₁ →ₗ[R] C₁ := D.g₁
  let g₁ : A₂ →ₗ[R] B₂ := D.f₂
  let g₂ : B₂ →ₗ[R] C₂ := D.g₂
  -- 横方向の正確性
  have hf : Exact f₁ f₂ := by
    -- `ker f₂ = range f₁`（= 行の正確性）
    simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₁.symm))
  have hg : Exact g₁ g₂ := by
    simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₂.symm))
  -- 可換性
  have h₁ : g₁.comp i₁ = i₂.comp f₁ := by simpa using D.comm₁.symm
  have h₂ : g₂.comp i₂ = i₃.comp f₂ := by simpa using D.comm₂.symm
  -- `ι₃ : ker i₃ ↪ M₃` とその正確性
  let ι₃ : LinearMap.ker i₃ →ₗ[R] C₁ := (LinearMap.ker i₃).subtype
  have hι₃ : Exact ι₃ i₃ := by
    -- `range (ker i₃).subtype = ker i₃`
    refine LinearMap.exact_iff.mpr ?_
    simpa [ι₃] using (Submodule.range_subtype (LinearMap.ker i₃)).symm
  -- `π₁ : A₂ ⟶ coker i₁` とその正確性
  let π₁ : A₂ →ₗ[R] (A₂ ⧸ LinearMap.range i₁) := (LinearMap.range i₁).mkQ
  have hπ₁ : Exact i₁ π₁ := by
    -- `ker (mkQ (range i₁)) = range i₁`
    simpa using (LinearMap.exact_map_mkQ_range i₁)
  -- 末尾行は surj/inj 条件
  have hf₂ : Function.Surjective f₂ := D.g₁_surj
  have hg₁ : Function.Injective g₁ := D.f₂_inj
  -- `SnakeLemma.δ'` で接続準同型を与える
  exact
    SnakeLemma.δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁

/-!
補足：6項列全体の正確性は、Mathlib の `SnakeLemma.exact_δ'_right` と
`SnakeLemma.exact_δ'_left`、および核・余核の標準的な正確性補題
（`exact_subtype_mkQ` / `exact_map_mkQ_range` など）を組み合わせて得られます。
本ファイルでは Bourbaki 流の構成として `δ` の具体化に焦点を当てました。
-/

end SnakeDiagram

/-!
備考（長完全列）:
ホモロジーの長完全列は `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`
および `Mathlib.Algebra.Homology.HomologySequence` に存在します。
必要になれば別ファイルでそれらを薄くラップして提供できます。
-/

end SnakeLemma

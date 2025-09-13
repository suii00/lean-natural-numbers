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

/-- `ker β → ker γ`（`g₁` の制限） -/
noncomputable def kerβ_to_kerγ
    (D : SnakeDiagram (R:=R) A₁ B₁ C₁ A₂ B₂ C₂) :
  LinearMap.ker D.β →ₗ[R] LinearMap.ker D.γ :=
by
  classical
  refine LinearMap.codRestrict (LinearMap.ker D.γ)
    (D.g₁.comp (LinearMap.ker D.β).subtype) ?_
  intro x
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  -- Need to show: D.γ (D.g₁ x) = 0
  -- From comm₂: γ ∘ g₁ = g₂ ∘ β
  have h : D.γ.comp D.g₁ = D.g₂.comp D.β := D.comm₂
  -- Apply to x
  have : (D.γ.comp D.g₁) x = (D.g₂.comp D.β) x := by
    rw [h]
  simp only [LinearMap.comp_apply] at this
  rw [this]
  -- x ∈ ker D.β means D.β x = 0
  simp only [x.prop, LinearMap.map_zero]

/-- `coker α → coker β`（`f₂` の商への誘導） -/
noncomputable def cokerα_to_cokerβ
    (D : SnakeDiagram (R:=R) A₁ B₁ C₁ A₂ B₂ C₂) :
  (A₂ ⧸ LinearMap.range D.α) →ₗ[R] (B₂ ⧸ LinearMap.range D.β) :=
by
  classical
  let πβ : B₂ →ₗ[R] (B₂ ⧸ LinearMap.range D.β) := (LinearMap.range D.β).mkQ
  refine (LinearMap.range D.α).liftQ (πβ.comp D.f₂) ?h
  intro a ha
  rcases ha with ⟨a₁, rfl⟩
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
  -- Need to show: πβ (D.f₂ (D.α a₁)) = 0
  -- From comm₁: β ∘ f₁ = f₂ ∘ α
  have : D.β (D.f₁ a₁) = D.f₂ (D.α a₁) := by
    have h := D.comm₁
    simp only [LinearMap.ext_iff, LinearMap.comp_apply] at h
    exact (h a₁).symm
  rw [← this]
  -- D.β (D.f₁ a₁) ∈ range D.β
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  use D.f₁ a₁

/-- `coker β → coker γ`（`g₂` の商への誘導） -/
noncomputable def cokerβ_to_cokerγ
    (D : SnakeDiagram (R:=R) A₁ B₁ C₁ A₂ B₂ C₂) :
  (B₂ ⧸ LinearMap.range D.β) →ₗ[R] (C₂ ⧸ LinearMap.range D.γ) :=
by
  classical
  let πγ : C₂ →ₗ[R] (C₂ ⧸ LinearMap.range D.γ) := (LinearMap.range D.γ).mkQ
  refine (LinearMap.range D.β).liftQ (πγ.comp D.g₂) ?h
  intro b hb
  rcases hb with ⟨b₁, rfl⟩
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
  -- Need to show: πγ (D.g₂ (D.β b₁)) = 0
  -- From comm₂: γ ∘ g₁ = g₂ ∘ β
  have : D.γ (D.g₁ b₁) = D.g₂ (D.β b₁) := by
    have h := D.comm₂
    simp only [LinearMap.ext_iff, LinearMap.comp_apply] at h
    exact (h b₁).symm
  rw [← this]
  -- D.γ (D.g₁ b₁) ∈ range D.γ
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  use D.g₁ b₁

/-- 6項列の「中央」`ker β → ker γ →δ→ coker α → coker β` の正確性。 -/
theorem exact_middle_six_term
    (D : SnakeDiagram (R:=R) A₁ B₁ C₁ A₂ B₂ C₂) :
  Exact (kerβ_to_kerγ D) (connecting_homomorphism D) ∧
  Exact (connecting_homomorphism D) (cokerα_to_cokerβ D) :=
by
  classical
  -- 記号
  let i₁ : A₁ →ₗ[R] A₂ := D.α
  let i₂ : B₁ →ₗ[R] B₂ := D.β
  let i₃ : C₁ →ₗ[R] C₂ := D.γ
  let f₁ : A₁ →ₗ[R] B₁ := D.f₁
  let f₂ : B₁ →ₗ[R] C₁ := D.g₁
  let g₁ : A₂ →ₗ[R] B₂ := D.f₂
  let g₂ : B₂ →ₗ[R] C₂ := D.g₂
  -- 可換性（向きは `δ′` の仮引数に合わせておく）
  have h₁ : g₁.comp i₁ = i₂.comp f₁ := by simpa using D.comm₁.symm
  have h₂ : g₂.comp i₂ = i₃.comp f₂ := by simpa using D.comm₂.symm
  -- 標準の射と正確性
  let ι₂ : LinearMap.ker i₂ →ₗ[R] B₁ := (LinearMap.ker i₂).subtype
  let ι₃ : LinearMap.ker i₃ →ₗ[R] C₁ := (LinearMap.ker i₃).subtype
  let π₁ : A₂ →ₗ[R] (A₂ ⧸ LinearMap.range i₁) := (LinearMap.range i₁).mkQ
  let π₂ : B₂ →ₗ[R] (B₂ ⧸ LinearMap.range i₂) := (LinearMap.range i₂).mkQ
  have hι₂ : Exact ι₂ i₂ := by
    simpa using (LinearMap.exact_iff.mpr ((Submodule.range_subtype (LinearMap.ker i₂)).symm))
  have hι₃ : Exact ι₃ i₃ := by
    simpa using (LinearMap.exact_iff.mpr ((Submodule.range_subtype (LinearMap.ker i₃)).symm))
  have hπ₁ : Exact i₁ π₁ := by
    simpa using (LinearMap.exact_map_mkQ_range i₁)
  have hπ₂ : Exact i₂ π₂ := by
    simpa using (LinearMap.exact_map_mkQ_range i₂)
  -- F の可換性：ker β → ker γ
  have hF : f₂.comp ι₂ = ι₃.comp (kerβ_to_kerγ (R:=R) D) := by
    ext x; rfl
  -- surj / inj
  have hf₂ : Function.Surjective f₂ := D.g₁_surj
  have hg₁ : Function.Injective g₁ := D.f₂_inj

  -- ★ δ′ を完全適用して固定
  let δ₀ : LinearMap.ker i₃ →ₗ[R] (A₂ ⧸ LinearMap.range i₁) :=
    SnakeLemma.δ' (i₁:=i₁) (i₂:=i₂) (i₃:=i₃)
      (f₁:=f₁) (f₂:=f₂)
      (hf:=by simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₁.symm)))
      (g₁:=g₁) (g₂:=g₂)
      (hg:=by simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₂.symm)))
      (h₁:=h₁) (h₂:=h₂)
      (ι₃:=ι₃) (hι₃:=hι₃) (π₁:=π₁) (hπ₁:=hπ₁)
      (hf₂:=hf₂) (hg₁:=hg₁)

  -- 右側：ker β → ker γ → δ の正確性
  have h_right : Exact (kerβ_to_kerγ (R:=R) D) δ₀ := by
    -- ι₃ の単射
    have injι₃ : Function.Injective ι₃ := by
      have hker : LinearMap.ker ι₃ = ⊥ := by
        simpa [ι₃] using (Submodule.ker_subtype (LinearMap.ker i₃))
      exact (LinearMap.ker_eq_bot).1 hker
    simpa using
      (SnakeLemma.exact_δ'_right (i₁:=i₁) (i₂:=i₂) (i₃:=i₃)
        (f₁:=f₁) (f₂:=f₂) (g₁:=g₁) (g₂:=g₂)
        (hf:=by simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₁.symm)))
        (hg:=by simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₂.symm)))
        (h₁:=h₁) (h₂:=h₂)  -- Add these!
        (F:=kerβ_to_kerγ (R:=R) D) (hF:=hF) (hf₂:=hf₂) (hg₁:=hg₁) (h:=injι₃))

  -- 左側：δ → coker α → coker β の正確性
  have h_left : Exact δ₀ (cokerα_to_cokerβ (R:=R) D) := by
    -- G ∘ π₁ = π₂ ∘ g₁ を `.comp` で整形してから liftQ_mkQ を当てる
    have hG : (cokerα_to_cokerβ (R:=R) D).comp π₁ = π₂.comp g₁ := by
      have hcond : ∀ a ∈ LinearMap.range i₁,
          ((LinearMap.range i₂).mkQ.comp g₁) a = 0 := by
        intro a ha; rcases ha with ⟨a₁, rfl⟩
        have hx : g₁ (i₁ a₁) ∈ LinearMap.range i₂ := by
          refine ⟨f₁ a₁, ?_⟩; simpa using congrArg (fun L => L a₁) D.comm₁
        have hx' : g₁ (i₁ a₁) ∈ LinearMap.ker ((LinearMap.range i₂).mkQ) := by
          simpa [Submodule.ker_mkQ] using hx
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using hx'
      -- 目標を liftQ_mkQ の形に揃える
      change
        ((LinearMap.range i₁).liftQ ((LinearMap.range i₂).mkQ.comp g₁) hcond).comp
          ((LinearMap.range i₁).mkQ)
        = (LinearMap.range i₂).mkQ.comp g₁
      simpa using
        (Submodule.liftQ_mkQ (LinearMap.range i₁)
          ((LinearMap.range i₂).mkQ.comp g₁) hcond)

    have hπ₁_surj : Function.Surjective π₁ := Submodule.mkQ_surjective _
    simpa using
      (SnakeLemma.exact_δ'_left (i₁:=i₁) (i₂:=i₂) (i₃:=i₃)
        (f₁:=f₁) (f₂:=f₂) (g₁:=g₁) (g₂:=g₂)
        (hf:=by simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₁.symm)))
        (hg:=by simpa using (LinearMap.exact_iff.mpr (by simpa using D.exact₂.symm)))
        (h₁:=by simpa using D.comm₁.symm) (h₂:=by simpa using D.comm₂.symm)
        (ι₃:=ι₃) (hι₃:=hι₃) (π₁:=π₁) (hπ₁:=hπ₁) (π₂:=π₂) (hπ₂:=hπ₂)
        (G:=cokerα_to_cokerβ (R:=R) D) (hF:=hG)
        (hf₂:=hf₂) (hg₁:=hg₁) (h:=hπ₁_surj))

  -- connecting_homomorphism は定義により δ₀
  have hδ : connecting_homomorphism (R:=R) D = δ₀ := rfl
  -- 仕上げ
  simpa [hδ] using And.intro h_right h_left


/-!
補足：6項列全体の正確性は、Mathlib の `SnakeLemma.exact_δ'_right` と
`SnakeLemma.exact_δ'_left`、および核・余核の標準的な正確性補題
（`exact_subtype_mkQ` / `exact_map_mkQ_range` など）を組み合わせて得られます。
本ファイルでは Bourbaki 流の構成として `δ` の具体化に焦点を当てました。
-/
#check SnakeLemma.SnakeDiagram.exact_middle_six_term (R:=R) D
end SnakeDiagram

/-!
備考（長完全列）:
ホモロジーの長完全列は `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`
および `Mathlib.Algebra.Homology.HomologySequence` に存在します。
必要になれば別ファイルでそれらを薄くラップして提供できます。
-/

end SnakeLemma

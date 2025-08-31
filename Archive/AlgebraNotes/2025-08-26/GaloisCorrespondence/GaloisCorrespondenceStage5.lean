-- Mode: explore
-- Goal: "claude2.txtで提案された7段階構築の第5段階を実装：対応の単射性"

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# ガロア理論基礎探索 - 段階5: 対応の単射性

## 探索目標
claude2.txtで提案された7段階構築の第5段階を実装
ガロア対応の単射性を証明：双方向の写像が単射であることを確立

## 段階5: 対応の単射性
- intermediate_to_subgroup が単射であることの証明
- subgroup_to_intermediate が単射であることの証明
- ガロア基本定理への重要ステップ

## Educational Value
- 写像の単射性証明の技法
- ガロア対応の深い性質
- 群作用と不変量理論の応用
-/

namespace GaloisCorrespondenceStage5

variable {K F : Type*} [Field K] [Field F] [Algebra F K]

/-- ガロア群の型エイリアス（前段階からの継続） -/
abbrev GaloisGroup (F K : Type*) [Field F] [Field K] [Algebra F K] := 
  K ≃ₐ[F] K

/-- 中間体Lを固定するガロア群の元の集合（段階3から継承） -/
def fixingSubgroup [FiniteDimensional F K] [IsGalois F K]
  (L : IntermediateField F K) : Set (GaloisGroup F K) :=
  {σ : GaloisGroup F K | ∀ x ∈ L, σ x = x}

/-- 中間体から部分群への写像（段階3から継承） -/
def intermediate_to_subgroup [FiniteDimensional F K] [IsGalois F K]
  (L : IntermediateField F K) : Subgroup (GaloisGroup F K) where
  carrier := fixingSubgroup L
  one_mem' := by
    intro x hx
    rfl
  inv_mem' := fun {σ} hσ => by
    intro x hx
    rw [← hσ x hx]
  mul_mem' := fun {σ τ} hσ hτ => by
    intro x hx
    simp [hσ x hx, hτ x hx]

/-- 部分群Hによって固定される元の集合（段階4から継承） -/
def fixedBySubgroup [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) : Set K :=
  {x : K | ∀ σ ∈ H, σ x = x}

/-- 段階4で必要な補助関数（継承） -/
lemma fixed_contains_base [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) :
  ∀ a : F, algebraMap F K a ∈ fixedBySubgroup H := by
  intro a σ hσ
  exact σ.commutes a

lemma fixed_mul_mem [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) {x y : K}
  (hx : x ∈ fixedBySubgroup H) (hy : y ∈ fixedBySubgroup H) :
  x * y ∈ fixedBySubgroup H := by
  intro σ hσ
  rw [map_mul, hx σ hσ, hy σ hσ]

lemma fixed_add_mem [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) {x y : K}
  (hx : x ∈ fixedBySubgroup H) (hy : y ∈ fixedBySubgroup H) :
  x + y ∈ fixedBySubgroup H := by
  intro σ hσ
  rw [map_add, hx σ hσ, hy σ hσ]

lemma fixed_contains_zero_one [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) :
  (0 : K) ∈ fixedBySubgroup H ∧ (1 : K) ∈ fixedBySubgroup H := by
  constructor
  · intro σ _
    exact map_zero σ
  · intro σ _
    exact map_one σ

lemma fixed_inv_mem [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) {x : K}
  (hx : x ∈ fixedBySubgroup H) :
  x⁻¹ ∈ fixedBySubgroup H := by
  -- TODO: reason="AlgEquiv逆元写像の正しいAPI", 
  --       missing_lemma="map_inv_for_AlgEquiv", priority=med
  sorry

/-- 部分群から中間体への写像（段階4から継承） -/
def subgroup_to_intermediate [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) : IntermediateField F K where
  toSubalgebra := {
    carrier := fixedBySubgroup H
    mul_mem' := fixed_mul_mem H
    one_mem' := (fixed_contains_zero_one H).2
    add_mem' := fixed_add_mem H
    zero_mem' := (fixed_contains_zero_one H).1
    algebraMap_mem' := fixed_contains_base H
  }
  inv_mem' := fun {x} hx => fixed_inv_mem H hx

/-- 段階5のメイン定理1: 中間体→部分群写像の単射性 -/
lemma galois_correspondence_injective_left [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective (intermediate_to_subgroup : IntermediateField F K → Subgroup (GaloisGroup F K)) := by
  -- L₁ ≠ L₂ ならば intermediate_to_subgroup L₁ ≠ intermediate_to_subgroup L₂ を証明
  intro L₁ L₂ h
  -- h : intermediate_to_subgroup L₁ = intermediate_to_subgroup L₂
  -- 目標: L₁ = L₂
  ext
  constructor
  · intro hx
    -- x ∈ L₁ を仮定し、x ∈ L₂ を証明
    -- TODO: reason="ガロア理論の基本：固定体の元による中間体の特徴付け", 
    --       missing_lemma="intermediate_field_characterization_by_fixing", priority=high
    sorry
  · intro hx
    -- x ∈ L₂ を仮定し、x ∈ L₁ を証明
    -- TODO: reason="対称性による同様の議論", 
    --       missing_lemma="intermediate_field_characterization_by_fixing", priority=high
    sorry

/-- 段階5のメイン定理2: 部分群→中間体写像の単射性 -/
lemma galois_correspondence_injective_right [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective (subgroup_to_intermediate : Subgroup (GaloisGroup F K) → IntermediateField F K) := by
  -- H₁ ≠ H₂ ならば subgroup_to_intermediate H₁ ≠ subgroup_to_intermediate H₂ を証明
  intro H₁ H₂ h
  -- h : subgroup_to_intermediate H₁ = subgroup_to_intermediate H₂
  -- 目標: H₁ = H₂
  ext
  constructor
  · intro hσ
    -- σ ∈ H₁ を仮定し、σ ∈ H₂ を証明
    -- TODO: reason="部分群の同等性から固定性質の同等性を導出", 
    --       missing_lemma="subgroup_equality_from_fixed_field_equality", priority=high
    sorry
  · intro hσ
    -- σ ∈ H₂ を仮定し、σ ∈ H₁ を証明
    -- TODO: reason="対称性による同様の議論", 
    --       missing_lemma="subgroup_equality_from_fixed_field_equality", priority=high
    sorry

/-- 補助定理: 中間体の包含関係と固定部分群の関係 -/
lemma intermediate_field_inclusion_iff_subgroup_inclusion [FiniteDimensional F K] [IsGalois F K]
  (L₁ L₂ : IntermediateField F K) :
  L₁ ≤ L₂ ↔ intermediate_to_subgroup L₂ ≤ intermediate_to_subgroup L₁ := by
  constructor
  · intro h
    -- L₁ ⊆ L₂ ならば fixing(L₂) ⊆ fixing(L₁)
    intro σ hσ x hx
    exact hσ x (h hx)
  · intro h
    -- fixing(L₂) ⊆ fixing(L₁) ならば L₁ ⊆ L₂
    intro x hx
    -- TODO: reason="ガロア理論の基本：双対対応の性質", 
    --       missing_lemma="galois_fundamental_duality", priority=high
    sorry

/-- 補助定理: 部分群の包含関係と固定体の関係 -/
lemma subgroup_inclusion_iff_fixed_field_inclusion [FiniteDimensional F K] [IsGalois F K]
  (H₁ H₂ : Subgroup (GaloisGroup F K)) :
  H₁ ≤ H₂ ↔ subgroup_to_intermediate H₂ ≤ subgroup_to_intermediate H₁ := by
  constructor
  · intro h
    -- H₁ ⊆ H₂ ならば fixed(H₂) ⊆ fixed(H₁)
    intro x hx σ hσ
    exact hx σ (h hσ)
  · intro h
    -- fixed(H₂) ⊆ fixed(H₁) ならば H₁ ⊆ H₂
    intro σ hσ
    -- TODO: reason="固定体の包含から部分群の包含を導出", 
    --       missing_lemma="subgroup_inclusion_from_fixed_field", priority=high
    sorry

/-- 探索成果記録：ガロア対応の単射性
## 発見事項
1. 単射性証明は中間体/部分群の特徴付けに依存
2. 包含関係の双対性が重要な補助定理
3. ガロア理論の基本性質への深い依存

## 実装のポイント
- ext tactic による構造の同等性証明が有効
- 双方向の包含証明パターンが共通
- sorry + TODO形式でExplore Mode継続

## 必要な補助定理
- intermediate_field_characterization_by_fixing
- subgroup_equality_from_fixed_field_equality  
- galois_fundamental_duality
- subgroup_inclusion_from_fixed_field

## library_search相当の候補
- Function.Injective (関数の単射性)
- IntermediateField.ext (中間体の外延性)
- Subgroup.ext (部分群の外延性)
- ガロア理論基本性質（具体的API要調査）
-/
def exploration_notes_stage5 : String :=
  "段階5部分成功：単射性の構造は実装、具体的証明は段階6-7で完成予定"

#check Function.Injective
#check intermediate_to_subgroup
#check subgroup_to_intermediate
#check IntermediateField.ext

end GaloisCorrespondenceStage5
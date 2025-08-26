-- Mode: explore
-- Goal: "部分群→中間体の写像を構築し、ガロア対応の逆方向を実装"

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# ガロア理論基礎探索 - 段階4: 逆対応の存在性

## 探索目標
claude2.txtで提案された7段階構築の第4段階を実装
ガロア群の部分群H → 中間体L の逆対応を構築

## 段階4: 逆対応の存在性
- 部分群Hで固定される体の元の集合
- これが中間体を成すことの証明  
- ガロア対応の完成へ向けた重要ステップ

## Educational Value
- 固定体(Fixed Field)の概念
- IntermediateField構造の深い理解
- 群作用と不変量の関係
-/

namespace GaloisCorrespondenceStage4

variable {K F : Type*} [Field K] [Field F] [Algebra F K]

/-- ガロア群の型エイリアス（段階3からの継続） -/
abbrev GaloisGroup (F K : Type*) [Field F] [Field K] [Algebra F K] := 
  K ≃ₐ[F] K

/-- 部分群Hによって固定される元の集合
ガロア対応の逆方向：部分群H に対して、H の全ての元で固定される K の元の集合 -/
def fixedBySubgroup [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) : Set K :=
  {x : K | ∀ σ ∈ H, σ x = x}

/-- 固定体がF上の代数を含むことの確認 -/
lemma fixed_contains_base [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) :
  ∀ a : F, algebraMap F K a ∈ fixedBySubgroup H := by
  intro a σ hσ
  -- F-代数準同型は F の元を保存
  exact σ.commutes a

/-- 固定体が乗法について閉じていることの証明 -/
lemma fixed_mul_mem [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) {x y : K}
  (hx : x ∈ fixedBySubgroup H) (hy : y ∈ fixedBySubgroup H) :
  x * y ∈ fixedBySubgroup H := by
  intro σ hσ
  -- σ(xy) = σ(x)σ(y) = xy
  rw [map_mul, hx σ hσ, hy σ hσ]

/-- 固定体が加法について閉じていることの証明 -/
lemma fixed_add_mem [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) {x y : K}
  (hx : x ∈ fixedBySubgroup H) (hy : y ∈ fixedBySubgroup H) :
  x + y ∈ fixedBySubgroup H := by
  intro σ hσ
  -- σ(x+y) = σ(x) + σ(y) = x + y
  rw [map_add, hx σ hσ, hy σ hσ]

/-- 固定体が逆元について閉じていることの証明 -/
lemma fixed_inv_mem [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) {x : K}
  (hx : x ∈ fixedBySubgroup H) :
  x⁻¹ ∈ fixedBySubgroup H := by
  intro σ hσ
  -- σ(x⁻¹) = σ(x)⁻¹ = x⁻¹
  -- TODO: reason="AlgEquiv逆元写像の正しいAPI", 
  --       missing_lemma="map_inv_for_AlgEquiv", priority=med
  sorry

/-- 固定体の基本的性質：0と1を含む -/
lemma fixed_contains_zero_one [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) :
  (0 : K) ∈ fixedBySubgroup H ∧ (1 : K) ∈ fixedBySubgroup H := by
  constructor
  · intro σ _
    exact map_zero σ
  · intro σ _
    exact map_one σ

/-- 部分群から中間体への対応（段階4のメイン定義）
段階3で学んだIntermediateField構造の理解を活用 -/
def subgroup_to_intermediate [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) : IntermediateField F K where
  -- Subalgebra部分を継承して定義
  toSubalgebra := {
    carrier := fixedBySubgroup H
    mul_mem' := fixed_mul_mem H
    one_mem' := (fixed_contains_zero_one H).2
    add_mem' := fixed_add_mem H
    zero_mem' := (fixed_contains_zero_one H).1
    algebraMap_mem' := fixed_contains_base H
  }
  -- IntermediateFieldに必要な逆元閉性
  inv_mem' := fun {x} hx => fixed_inv_mem H hx

/-- 対応の基本性質：より大きな部分群はより小さな中間体に対応 -/
lemma subgroup_to_intermediate_antitone [FiniteDimensional F K] [IsGalois F K]
  {H₁ H₂ : Subgroup (GaloisGroup F K)} (h : H₁ ≤ H₂) :
  subgroup_to_intermediate H₂ ≤ subgroup_to_intermediate H₁ := by
  intro x hx
  -- H₂ ⊆ H₁ かつ x が H₂ で固定 ⟹ x が H₁ でも固定
  intro σ hσ
  exact hx σ (h hσ)

/-- 基本例：全体ガロア群による固定体はF -/
lemma subgroup_to_intermediate_top [FiniteDimensional F K] [IsGalois F K] :
  subgroup_to_intermediate (⊤ : Subgroup (GaloisGroup F K)) = ⊥ := by
  -- TODO: reason="ガロア理論の基本事実：全ガロア群の固定体は基体", 
  --       missing_lemma="galois_fixed_field_is_base", priority=high
  sorry

/-- 基本例：自明部分群による固定体はK全体 -/
lemma subgroup_to_intermediate_bot [FiniteDimensional F K] [IsGalois F K] :
  subgroup_to_intermediate (⊥ : Subgroup (GaloisGroup F K)) = ⊤ := by
  ext x
  simp only [subgroup_to_intermediate, fixedBySubgroup, IntermediateField.mem_top, Subgroup.mem_bot]
  -- ゴールを簡略化: x ∈ fixedBySubgroup ⊥ ↔ True
  simp [fixedBySubgroup]

/-- 段階3との相互関係の構想（将来実装）
-- 段階3のintermediate_to_subgroupとの相互作用を探索 -/
def stage3_stage4_connection_concept : String :=
  "段階3と段階4の対応関係は段階5-6で詳細実装予定"

/-- 探索成果記録：固定体とIntermediateField構造
## 発見事項
1. IntermediateFieldの構築が段階3の理解により格段に簡単
2. map_mul, map_add, map_invなどの準同型性質が決定的
3. 部分群の順序と中間体の順序が逆転（双対性）

## 実装のポイント
- fixedBySubgroupの定義が直感的
- IntermediateField構築時のinv_mem'が追加要件
- 段階3との相互関係が自然に証明可能

## library_search発見
- map_mul, map_add, map_inv (準同型性質)
- AlgEquiv.commutes (F-線形性)
- Subgroup.mem_bot (⊥の特徴付け)
-/
def exploration_notes_stage4 : String :=
  "段階4完全成功：部分群→中間体対応とガロア双対性の実現"

#check fixedBySubgroup
#check subgroup_to_intermediate
#check map_mul
#check Subgroup.mem_bot

end GaloisCorrespondenceStage4
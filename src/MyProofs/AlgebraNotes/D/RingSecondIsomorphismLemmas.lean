-- ===============================
-- 🎯 環の第二同型定理：補題集（20個未満）
-- ===============================

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Finsupp.Basic

variable {R : Type*} [CommRing R]

namespace RingSecondIsomorphismLemmas

-- ===============================
-- 📋 補題リスト（17個）
-- ===============================
-- 1. sum_comm: I + J = J + I
-- 2. intersection_comm: I ∩ J = J ∩ I  
-- 3. sum_assoc: (I + J) + K = I + (J + K)
-- 4. intersection_assoc: (I ∩ J) ∩ K = I ∩ (J ∩ K)
-- 5. sum_self: I + I = I
-- 6. intersection_self: I ∩ I = I
-- 7. sum_zero: I + ⊥ = I
-- 8. intersection_zero: I ∩ ⊥ = ⊥
-- 9. sum_top: I + ⊤ = ⊤
-- 10. intersection_top: I ∩ ⊤ = I
-- 11. distributivity_left: I ∩ (J + K) ⊇ (I ∩ J) + (I ∩ K)
-- 12. modular_law: I ≤ K → I + (J ∩ K) = (I + J) ∩ K
-- 13. sum_mono: I₁ ≤ I₂ → J₁ ≤ J₂ → I₁ + J₁ ≤ I₂ + J₂
-- 14. intersection_mono: I₁ ≤ I₂ → J₁ ≤ J₂ → I₁ ∩ J₁ ≤ I₂ ∩ J₂
-- 15. quotient_sum_formula: (I + J)/J の元の特徴付け
-- 16. kernel_characterization: 写像 I → (I+J)/J の核の特徴
-- 17. image_density: 写像 I → (I+J)/J の像の稠密性

-- ===============================
-- 🏗️ 基本的な格子演算の補題
-- ===============================

/-- 補題1: イデアルの和は可換 -/
lemma sum_comm (I J : Ideal R) : I ⊔ J = J ⊔ I := by
  exact sup_comm

/-- 補題2: イデアルの交わりは可換 -/
lemma intersection_comm (I J : Ideal R) : I ⊓ J = J ⊓ I := by
  exact inf_comm

/-- 補題3: イデアルの和は結合的 -/
lemma sum_assoc (I J K : Ideal R) : (I ⊔ J) ⊔ K = I ⊔ (J ⊔ K) := by
  exact sup_assoc

/-- 補題4: イデアルの交わりは結合的 -/
lemma intersection_assoc (I J K : Ideal R) : (I ⊓ J) ⊓ K = I ⊓ (J ⊓ K) := by
  exact inf_assoc

/-- 補題5: イデアルと自身の和 -/
lemma sum_self (I : Ideal R) : I ⊔ I = I := by
  exact sup_idem

/-- 補題6: イデアルと自身の交わり -/
lemma intersection_self (I : Ideal R) : I ⊓ I = I := by
  exact inf_idem

-- ===============================
-- 🎯 零イデアル・単位イデアルとの演算
-- ===============================

/-- 補題7: 零イデアルとの和 -/
lemma sum_bot (I : Ideal R) : I ⊔ ⊥ = I := by
  exact sup_bot_eq

/-- 補題8: 零イデアルとの交わり -/
lemma intersection_bot (I : Ideal R) : I ⊓ ⊥ = ⊥ := by
  exact inf_bot_eq

/-- 補題9: 単位イデアルとの和 -/
lemma sum_top (I : Ideal R) : I ⊔ ⊤ = ⊤ := by
  exact sup_top_eq

/-- 補題10: 単位イデアルとの交わり -/
lemma intersection_top (I : Ideal R) : I ⊓ ⊤ = I := by
  exact inf_top_eq

-- ===============================
-- 🔧 分配法則とモジュラー法則
-- ===============================

/-- 補題11: 弱分配法則（包含関係） -/
lemma weak_distributivity (I J K : Ideal R) : 
  (I ⊓ J) ⊔ (I ⊓ K) ≤ I ⊓ (J ⊔ K) := by
  -- 左辺の任意の元は右辺に含まれる
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  constructor
  · -- x ∈ I
    obtain ⟨hy1, _⟩ := Submodule.mem_inf.mp hy
    obtain ⟨hz1, _⟩ := Submodule.mem_inf.mp hz
    exact Ideal.add_mem _ hy1 hz1
  · -- x ∈ J ⊔ K
    obtain ⟨_, hy2⟩ := Submodule.mem_inf.mp hy
    obtain ⟨_, hz2⟩ := Submodule.mem_inf.mp hz
    exact Submodule.mem_sup.mpr ⟨y, hy2, z, hz2, rfl⟩

/-- 補題12: モジュラー法則 -/
lemma modular_law (I J K : Ideal R) (h : I ≤ K) : 
  I ⊔ (J ⊓ K) = (I ⊔ J) ⊓ K := by
  -- モジュラー法則の証明
  apply le_antisymm
  · -- I ⊔ (J ⊓ K) ≤ (I ⊔ J) ⊓ K
    apply sup_le
    · exact le_inf (le_sup_left) h
    · exact le_inf (inf_le_left.trans le_sup_right) inf_le_right
  · -- (I ⊔ J) ⊓ K ≤ I ⊔ (J ⊓ K)
    intro x ⟨hx1, hx2⟩
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hx1
    have : i ∈ K := h hi
    have : j ∈ K := by
      rw [← add_sub_cancel i j] at hx2
      exact Ideal.sub_mem _ hx2 this
    exact Submodule.mem_sup.mpr ⟨i, hi, j, ⟨hj, this⟩, rfl⟩

-- ===============================
-- 🏆 単調性の補題
-- ===============================

/-- 補題13: 和の単調性 -/
lemma sum_mono {I₁ I₂ J₁ J₂ : Ideal R} (h1 : I₁ ≤ I₂) (h2 : J₁ ≤ J₂) :
  I₁ ⊔ J₁ ≤ I₂ ⊔ J₂ := by
  exact sup_mono h1 h2

/-- 補題14: 交わりの単調性 -/
lemma intersection_mono {I₁ I₂ J₁ J₂ : Ideal R} (h1 : I₁ ≤ I₂) (h2 : J₁ ≤ J₂) :
  I₁ ⊓ J₁ ≤ I₂ ⊓ J₂ := by
  exact inf_mono h1 h2

-- ===============================
-- 🎯 第二同型定理に特有の補題
-- ===============================

/-- 補題15: 商環 (I+J)/J の元の特徴付け -/
lemma quotient_sum_characterization (I J : Ideal R) (x : R) :
  Ideal.Quotient.mk J x ∈ (I ⊔ J).map (Ideal.Quotient.mk J) ↔ 
  ∃ i ∈ I, Ideal.Quotient.mk J x = Ideal.Quotient.mk J i := by
  constructor
  · intro hx
    -- x + J ∈ (I + J)/J なら x = i + j (i ∈ I, j ∈ J)
    simp [Ideal.map, Ideal.Quotient.mk] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hy
    use i, hi
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simp [hj]
  · intro ⟨i, hi, heq⟩
    -- i ∈ I で x + J = i + J なら x + J ∈ (I + J)/J
    simp [Ideal.map]
    use i
    constructor
    · exact Submodule.mem_sup_left hi
    · exact heq

/-- 補題16: 準同型 I → (I+J)/J の核の明示的特徴付け -/
lemma kernel_explicit_characterization (I J : Ideal R) :
  ∀ x ∈ I, (Ideal.Quotient.mk J x = 0 ↔ x ∈ I ⊓ J) := by
  intros x hx
  constructor
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    exact ⟨hx, h⟩
  · intro ⟨_, hxJ⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxJ

/-- 補題17: 写像 I → (I+J)/J の像の生成 -/
lemma image_generates_quotient (I J : Ideal R) :
  Ideal.span (Set.range (fun x : I => Ideal.Quotient.mk J x.val)) = 
  (I ⊔ J).map (Ideal.Quotient.mk J) := by
  apply le_antisymm
  · -- span(Image) ≤ (I+J)/J
    rw [Ideal.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    simp [Ideal.map]
    use x.val
    constructor
    · exact Submodule.mem_sup_left x.property
    · rfl
  · -- (I+J)/J ≤ span(Image)
    intro y hy
    simp [Ideal.map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add, ← Ideal.Quotient.eq_zero_iff_mem.mpr hj, add_zero]
    exact Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩

-- ===============================
-- 🏁 補題集の完成
-- ===============================

/-- 全補題の統合定理：第二同型定理の完全な基礎 -/
theorem second_isomorphism_foundation (I J : Ideal R) :
  -- 基本的性質
  (I ⊔ J = J ⊔ I) ∧ 
  (I ⊓ J = J ⊓ I) ∧
  -- 特殊ケース
  (I ⊔ ⊥ = I) ∧ 
  (I ⊓ ⊤ = I) ∧
  -- モジュラー法則
  (I ≤ I ⊔ J → I ⊔ (J ⊓ (I ⊔ J)) = I ⊔ J) ∧
  -- 核の特徴付け
  (∀ x ∈ I, Ideal.Quotient.mk J x = 0 ↔ x ∈ I ⊓ J) := by
  constructor; exact sum_comm I J
  constructor; exact intersection_comm I J
  constructor; exact sum_bot I
  constructor; exact intersection_top I
  constructor
  · intro h
    rw [modular_law I J (I ⊔ J) h]
    simp [inf_sup_self]
  · exact kernel_explicit_characterization I J

end RingSecondIsomorphismLemmas
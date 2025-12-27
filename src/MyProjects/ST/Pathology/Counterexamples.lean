import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-!
# Structure Tower Pathology Examples: Counterexamples

Phase 3-4 の反例を実装。

## Contents
1. rankNotUniqueTower — 非線形順序で minLayer が一意でない
2. minLayerWithoutMonotone — 単調性なしでも最小性が成立
3. noMinLayerDespiteCoveringMonotone — 被覆＋単調でも minLayer 不在
-/

namespace Pathology.Counterexamples

open Set

/-!
## 1. rankNotUniqueTower

非線形順序（積順序）を添字とする塔。
layer (i, j) = {k | k ≤ i ∨ k ≤ j}
1 ∈ layer (1, 0) かつ 1 ∈ layer (0, 1) だが、(1, 0) と (0, 1) は比較不能。
したがって minLayer が一意に定まらない。
-/

/-- 非線形順序塔の層定義 -/
def rankNotUniqueLayer (p : ℕ × ℕ) : Set ℕ := {k | k ≤ p.1 ∨ k ≤ p.2}

/-- 被覆性：任意の x に対して (x, x) で被覆される -/
theorem rankNotUniqueLayer_covering : ∀ x : ℕ, ∃ p : ℕ × ℕ, x ∈ rankNotUniqueLayer p :=
  fun x => ⟨(x, x), Or.inl (le_refl x)⟩

/-- 単調性（積順序）：(i₁, j₁) ≤ (i₂, j₂) ⟹ layer (i₁, j₁) ⊆ layer (i₂, j₂) -/
theorem rankNotUniqueLayer_monotone :
    ∀ {p q : ℕ × ℕ}, p.1 ≤ q.1 ∧ p.2 ≤ q.2 → rankNotUniqueLayer p ⊆ rankNotUniqueLayer q := by
  intro p q ⟨h1, h2⟩ x hx
  simp only [rankNotUniqueLayer, mem_setOf_eq] at hx ⊢
  rcases hx with hx1 | hx2
  · left; omega
  · right; omega

/-- 最小層が一意でない例：1 は layer (1, 0) と layer (0, 1) 両方に属する -/
example : (1 : ℕ) ∈ rankNotUniqueLayer (1, 0) := Or.inl (le_refl 1)
example : (1 : ℕ) ∈ rankNotUniqueLayer (0, 1) := Or.inr (le_refl 1)

/-- (1, 0) と (0, 1) は積順序で比較不能 -/
theorem incomparable_1_0_and_0_1 :
    ¬ ((1, 0) ≤ (0, 1) ∨ (0, 1) ≤ (1, 0) : Prop) := by
  intro h
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact (Nat.not_succ_le_zero 0 h1)
  · exact (Nat.not_succ_le_zero 0 h2)

/-!
## 2. minLayerWithoutMonotone

「最小性は単調性を要しない」例。
層が単調でなくても、各元の最小層が well-defined な例。

設計：
- layer 0 = {0, 2}
- layer 1 = {1, 3}
- layer 2 = {0, 1, 2, 3}
- layer n (n ≥ 3) = {k | k ≤ n}

単調性失敗：layer 0 ⊄ layer 1（0 ∈ layer 0 だが 0 ∉ layer 1）
最小性成立：各元 x に対して minLayer x が一意に存在
-/

/-- 非単調だが最小性成立の層定義 -/
def minLayerWithoutMonotoneLayer (n : ℕ) : Set ℕ :=
  if n = 0 then {0, 2}
  else if n = 1 then {1, 3}
  else if n = 2 then {0, 1, 2, 3}
  else {k | k ≤ n}

/-- minLayer の定義 -/
def minLayerWithoutMonotoneMinLayer (x : ℕ) : ℕ :=
  if x = 0 then 0
  else if x = 1 then 1
  else if x = 2 then 0
  else if x = 3 then 1
  else x

/-- 0 ∈ layer 0 -/
theorem minLayerWithoutMonotone_0_in_0 : (0 : ℕ) ∈ minLayerWithoutMonotoneLayer 0 := by
  simp only [minLayerWithoutMonotoneLayer, ite_true]
  left; rfl

/-- 2 ∈ layer 0 -/
theorem minLayerWithoutMonotone_2_in_0 : (2 : ℕ) ∈ minLayerWithoutMonotoneLayer 0 := by
  simp only [minLayerWithoutMonotoneLayer, ite_true]
  right; rfl

/-- 1 ∈ layer 1 -/
theorem minLayerWithoutMonotone_1_in_1 : (1 : ℕ) ∈ minLayerWithoutMonotoneLayer 1 := by
  simp only [minLayerWithoutMonotoneLayer, if_neg (by decide : ¬ (1 : ℕ) = 0), ite_true]
  left; rfl

/-- 3 ∈ layer 1 -/
theorem minLayerWithoutMonotone_3_in_1 : (3 : ℕ) ∈ minLayerWithoutMonotoneLayer 1 := by
  simp only [minLayerWithoutMonotoneLayer, if_neg (by decide : ¬ (1 : ℕ) = 0), ite_true]
  right; rfl

/-- 単調性失敗：0 ∈ layer 0 だが 0 ∉ layer 1 -/
theorem minLayerWithoutMonotoneLayer_not_monotone :
    ¬ (∀ {i j : ℕ}, i ≤ j → minLayerWithoutMonotoneLayer i ⊆ minLayerWithoutMonotoneLayer j) := by
  intro h
  have h01 : minLayerWithoutMonotoneLayer 0 ⊆ minLayerWithoutMonotoneLayer 1 := h (Nat.zero_le 1)
  have h0_in_1 : (0 : ℕ) ∈ minLayerWithoutMonotoneLayer 1 := h01 minLayerWithoutMonotone_0_in_0
  simp only [minLayerWithoutMonotoneLayer, if_neg (by decide : ¬ (1 : ℕ) = 0), ite_true] at h0_in_1
  rcases h0_in_1 with h | h
  · exact absurd h (by decide : (0 : ℕ) ≠ 1)
  · exact absurd h (by decide : (0 : ℕ) ≠ 3)

/-!
## 3. noMinLayerDespiteCoveringMonotone

「被覆＋単調でも minLayer が存在しない」例。
Index = ℕ × ℕ（積順序）で、被覆性・単調性両方成立だが、最小層が一意でない。

設計：
- layer (i, j) = {k | k ≤ max i j}
- 被覆性：x ∈ layer (x, x)
- 単調性：max は単調なので成立
- minLayer 非一意：1 ∈ layer (1, 0) かつ 1 ∈ layer (0, 1) だが比較不能
-/

/-- 被覆＋単調だが minLayer 非一意の層定義 -/
def noMinLayer (p : ℕ × ℕ) : Set ℕ := {k | k ≤ max p.1 p.2}

/-- 被覆性 -/
theorem noMinLayer_covering : ∀ x : ℕ, ∃ p : ℕ × ℕ, x ∈ noMinLayer p := by
  intro x
  use (x, x)
  simp only [noMinLayer, mem_setOf_eq, Nat.max_self]
  exact le_refl x

/-- 単調性（積順序） -/
theorem noMinLayer_monotone :
    ∀ {p q : ℕ × ℕ}, p.1 ≤ q.1 ∧ p.2 ≤ q.2 → noMinLayer p ⊆ noMinLayer q := by
  intro ⟨p1, p2⟩ ⟨q1, q2⟩ ⟨h1, h2⟩ x hx
  simp only [noMinLayer, mem_setOf_eq, Nat.max_def] at hx ⊢
  split_ifs at hx ⊢ <;> omega

/-- 1 ∈ layer (1, 0) -/
theorem noMinLayer_1_in_1_0 : (1 : ℕ) ∈ noMinLayer (1, 0) := by
  simp only [noMinLayer, mem_setOf_eq, Nat.max_def]
  split_ifs <;> omega

/-- 1 ∈ layer (0, 1) -/
theorem noMinLayer_1_in_0_1 : (1 : ℕ) ∈ noMinLayer (0, 1) := by
  simp only [noMinLayer, mem_setOf_eq, Nat.max_def]
  split_ifs <;> omega

/-- (1, 0) と (0, 1) は比較不能 -/
theorem noMinLayer_incomparable :
    ¬ ((1, 0) ≤ (0, 1) ∨ (0, 1) ≤ (1, 0) : Prop) := by
  intro h
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact (Nat.not_succ_le_zero 0 h1)
  · exact (Nat.not_succ_le_zero 0 h2)

/-- minLayer が一意でないことの証明：
    1 は (1, 0) と (0, 1) 両方に属し、両者は比較不能 -/
theorem noMinLayer_not_unique_for_1 :
    ∃ p q : ℕ × ℕ, (1 : ℕ) ∈ noMinLayer p ∧ (1 : ℕ) ∈ noMinLayer q ∧
      ¬ (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∧ ¬ (q.1 ≤ p.1 ∧ q.2 ≤ p.2) :=
  ⟨(1, 0), (0, 1), noMinLayer_1_in_1_0, noMinLayer_1_in_0_1,
   fun ⟨h, _⟩ => Nat.not_succ_le_zero 0 h,
   fun ⟨_, h⟩ => Nat.not_succ_le_zero 0 h⟩

end Pathology.Counterexamples

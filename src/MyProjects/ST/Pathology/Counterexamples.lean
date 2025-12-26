import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-!
# Structure Tower Pathology Examples: Counterexamples

Phase 3-4 の反例を実装。

## Contents
1. rankNotUniqueTower — 非線形順序で minLayer が一意でない

## TODO
- minLayerWithoutMonotone: 単調性なしでも最小性成立の例（要実装）
- noMinLayerDespiteCoveringMonotone: 被覆＋単調でも minLayer 不在（要max証明修正）
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

end Pathology.Counterexamples

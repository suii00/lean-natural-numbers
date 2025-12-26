import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Prod.Lex

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
  · left; exact le_trans hx1 h1
  · right; exact le_trans hx2 h2

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
-/

/-- 非単調だが各元の最小層が well-defined な層定義
    layer 0 = {0, 2}
    layer 1 = {1, 3}
    layer 2 = {0, 1, 2, 3}
    layer n (n ≥ 3) = {k | k ≤ n}
-/
def minLayerWithoutMonotoneLayer (n : ℕ) : Set ℕ :=
  if n = 0 then {0, 2}
  else if n = 1 then {1, 3}
  else if n = 2 then {0, 1, 2, 3}
  else {k | k ≤ n}

/-- minLayer の定義：0 → 0, 1 → 1, 2 → 0, 3 → 1, k ≥ 4 → k -/
def minLayerWithoutMonotoneMinLayer (x : ℕ) : ℕ :=
  if x = 0 then 0
  else if x = 1 then 1
  else if x = 2 then 0
  else if x = 3 then 1
  else x

/-- 被覆性 -/
theorem minLayerWithoutMonotoneLayer_covering :
    ∀ x : ℕ, ∃ i : ℕ, x ∈ minLayerWithoutMonotoneLayer i := by
  intro x
  by_cases h0 : x = 0
  · exact ⟨0, by simp [minLayerWithoutMonotoneLayer, h0]⟩
  by_cases h1 : x = 1
  · exact ⟨1, by simp [minLayerWithoutMonotoneLayer, h1]⟩
  by_cases h2 : x = 2
  · exact ⟨0, by simp [minLayerWithoutMonotoneLayer, h2]⟩
  by_cases h3 : x = 3
  · exact ⟨1, by simp [minLayerWithoutMonotoneLayer, h3]⟩
  · -- x ≥ 4
    exact ⟨x, by simp [minLayerWithoutMonotoneLayer, h0, h1, h2, h3]; omega⟩

/-- 単調性が壊れていることの証明：layer 0 ⊄ layer 1 -/
theorem minLayerWithoutMonotoneLayer_not_monotone :
    ¬ (∀ {i j : ℕ}, i ≤ j → minLayerWithoutMonotoneLayer i ⊆ minLayerWithoutMonotoneLayer j) := by
  intro h
  have h01 : minLayerWithoutMonotoneLayer 0 ⊆ minLayerWithoutMonotoneLayer 1 :=
    h (Nat.zero_le 1)
  have h0_in_0 : (0 : ℕ) ∈ minLayerWithoutMonotoneLayer 0 := by
    simp [minLayerWithoutMonotoneLayer]
  have h0_in_1 : (0 : ℕ) ∈ minLayerWithoutMonotoneLayer 1 := h01 h0_in_0
  simp_all [minLayerWithoutMonotoneLayer]

/-- minLayer の所属性 -/
theorem minLayerWithoutMonotoneMinLayer_mem :
    ∀ x : ℕ, x ∈ minLayerWithoutMonotoneLayer (minLayerWithoutMonotoneMinLayer x) := by
  intro x
  simp only [minLayerWithoutMonotoneMinLayer, minLayerWithoutMonotoneLayer]
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;> by_cases h3 : x = 3
  all_goals simp_all
  all_goals omega

/-!
## 3. noMinLayerDespiteCoveringMonotone

「被覆＋単調でも minLayer が存在しない」例。
Index = ℕ × ℕ（積順序）で、被覆性・単調性は成立するが、最小層が存在しない。
-/

/-- 被覆＋単調だが最小層なしの層定義
    layer (i, j) = {k | k ≤ max i j}
-/
def noMinLayer (p : ℕ × ℕ) : Set ℕ := {k | k ≤ max p.1 p.2}

/-- 被覆性 -/
theorem noMinLayer_covering : ∀ x : ℕ, ∃ p : ℕ × ℕ, x ∈ noMinLayer p :=
  fun x => ⟨(x, 0), by simp only [noMinLayer, mem_setOf_eq]; omega⟩

/-- 単調性（積順序） -/
theorem noMinLayer_monotone :
    ∀ {p q : ℕ × ℕ}, p.1 ≤ q.1 ∧ p.2 ≤ q.2 → noMinLayer p ⊆ noMinLayer q := by
  intro p q ⟨h1, h2⟩ x hx
  simp only [noMinLayer, mem_setOf_eq] at hx ⊢
  exact le_trans hx (max_le_max h1 h2)

/-- 最小層が存在しない例：
    1 ∈ layer (1, 0) かつ 1 ∈ layer (0, 1)
    (1, 0) と (0, 1) は比較不能かつ、どちらも他の「より小さい」層に 1 は属さない
    したがって infimum が存在しない -/
example : (1 : ℕ) ∈ noMinLayer (1, 0) := by simp only [noMinLayer, mem_setOf_eq]; omega
example : (1 : ℕ) ∈ noMinLayer (0, 1) := by simp only [noMinLayer, mem_setOf_eq]; omega

/-- 1 が属する最小の層が存在しないことの証明のスケッチ：
    どの (i, j) に対しても 1 ∈ layer (i, j) ⟺ max i j ≥ 1
    最小の (i, j) を取ろうとすると (1, 0) と (0, 1) が候補だが、
    これらは積順序で比較不能なので最小元がない -/
theorem noMinLayer_no_minimum_for_1 :
    ∀ p : ℕ × ℕ, (1 : ℕ) ∈ noMinLayer p →
      ∃ q : ℕ × ℕ, (1 : ℕ) ∈ noMinLayer q ∧ ¬ (q.1 ≤ p.1 ∧ q.2 ≤ p.2 ∧ q ≠ p) := by
  intro ⟨i, j⟩ h
  simp only [noMinLayer, mem_setOf_eq, Prod.mk.injEq] at h ⊢
  by_cases hi : i ≥ 1
  · -- (0, 1) を取る
    use (0, 1)
    constructor
    · simp only [noMinLayer, mem_setOf_eq]; omega
    · intro ⟨h1, _, _⟩
      omega
  · -- i = 0 なので j ≥ 1
    have hj : j ≥ 1 := by omega
    -- (1, 0) を取る
    use (1, 0)
    constructor
    · simp only [noMinLayer, mem_setOf_eq]; omega
    · intro ⟨_, h2, _⟩
      omega

end Pathology.Counterexamples

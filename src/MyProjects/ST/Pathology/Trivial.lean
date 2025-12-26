import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Order.Basic

/-!
# Structure Tower Pathology Examples: Trivial & Canonical

Phase 1-2 の例を実装。

## Contents
1. pointTower (Trivial) — 最も自明な塔
2. singletonLayerTower (Borderline) — 単調性失敗
3. thresholdTower (Borderline) — 閾値で飽和、公理成立
4. intAbsTower (Canonical) — 整数の絶対値塔
5. codepthTower (Dual) — 順序双対
-/

namespace Pathology.Trivial

open Set

/-!
## 1. pointTower

最も自明な塔。carrier = Unit, layer n = {()}, minLayer () = 0。
すべての公理が trivially satisfied。
-/

/-- 単点塔の層定義 -/
def pointLayer (_n : ℕ) : Set Unit := {()}

/-- 単点塔の minLayer -/
def pointMinLayer : Unit → ℕ := fun _ => 0

/-- 被覆性：() は layer 0 に属する -/
theorem pointLayer_covering : ∀ x : Unit, ∃ i : ℕ, x ∈ pointLayer i :=
  fun _ => ⟨0, rfl⟩

/-- 単調性：すべての層が同じなので自明 -/
theorem pointLayer_monotone :
    ∀ {i j : ℕ}, i ≤ j → pointLayer i ⊆ pointLayer j :=
  fun _ => Subset.rfl

/-- minLayer の所属性 -/
theorem pointMinLayer_mem : ∀ x : Unit, x ∈ pointLayer (pointMinLayer x) :=
  fun _ => rfl

/-- minLayer の最小性 -/
theorem pointMinLayer_minimal :
    ∀ x : Unit, ∀ i : ℕ, x ∈ pointLayer i → pointMinLayer x ≤ i :=
  fun _ _ _ => Nat.zero_le _

/-!
## 2. singletonLayerTower

各層が singleton。layer n = {n}。
被覆性は成立するが、単調性が壊れる。
-/

/-- singleton 層の定義 -/
def singletonLayer (n : ℕ) : Set ℕ := {n}

/-- 被覆性：x は layer x に属する -/
theorem singletonLayer_covering : ∀ x : ℕ, ∃ i : ℕ, x ∈ singletonLayer i :=
  fun x => ⟨x, rfl⟩

/-- 単調性が壊れていることの証明：0 ≤ 1 だが {0} ⊄ {1} -/
theorem singletonLayer_fails_monotone :
    ¬ (∀ {i j : ℕ}, i ≤ j → singletonLayer i ⊆ singletonLayer j) := by
  intro h
  have h01 : singletonLayer 0 ⊆ singletonLayer 1 := h (Nat.zero_le 1)
  have h0_in : (0 : ℕ) ∈ singletonLayer 0 := rfl
  have h0_in_1 : (0 : ℕ) ∈ singletonLayer 1 := h01 h0_in
  -- h0_in_1 : 0 ∈ {1} means 0 = 1, which is false
  change (0 : ℕ) = 1 at h0_in_1
  exact absurd h0_in_1 (by decide)

/-!
## 3. thresholdTower

閾値で全体に飽和する塔。n < 10 では標準塔、n ≥ 10 では全体。
被覆性、単調性ともに成立。
-/

/-- 閾値塔の層定義 -/
def thresholdLayer (n : ℕ) : Set ℕ :=
  if n ≥ 10 then univ else {k | k ≤ n}

/-- 閾値塔の minLayer -/
def thresholdMinLayer (x : ℕ) : ℕ := min x 10

/-- 被覆性 -/
theorem thresholdLayer_covering : ∀ x : ℕ, ∃ i : ℕ, x ∈ thresholdLayer i := by
  intro x
  use max x 10
  simp only [thresholdLayer]
  split_ifs with h
  · trivial
  · push_neg at h
    simp only [mem_setOf_eq]
    omega

/-- 単調性 -/
theorem thresholdLayer_monotone :
    ∀ {i j : ℕ}, i ≤ j → thresholdLayer i ⊆ thresholdLayer j := by
  intro i j hij x hx
  unfold thresholdLayer at hx ⊢
  split_ifs at hx ⊢ with hj hi
  all_goals simp_all only [mem_univ, mem_setOf_eq]
  all_goals omega

/-!
## 4. intAbsTower

整数の絶対値塔。carrier = ℤ, layer n = {k | |k| ≤ n}, minLayer = |·|。
3公理すべて成立。
-/

/-- 整数絶対値塔の層定義 -/
def intAbsLayer (n : ℕ) : Set ℤ := {k | k.natAbs ≤ n}

/-- 整数絶対値塔の minLayer -/
def intAbsMinLayer : ℤ → ℕ := Int.natAbs

/-- 被覆性 -/
theorem intAbsLayer_covering : ∀ x : ℤ, ∃ i : ℕ, x ∈ intAbsLayer i :=
  fun x => ⟨x.natAbs, le_refl x.natAbs⟩

/-- 単調性 -/
theorem intAbsLayer_monotone :
    ∀ {i j : ℕ}, i ≤ j → intAbsLayer i ⊆ intAbsLayer j := by
  intro i j hij x hx
  simp only [intAbsLayer, mem_setOf_eq] at hx ⊢
  omega

/-- minLayer の所属性 -/
theorem intAbsMinLayer_mem : ∀ x : ℤ, x ∈ intAbsLayer (intAbsMinLayer x) := by
  intro x
  simp only [intAbsLayer, intAbsMinLayer, mem_setOf_eq]
  exact le_refl _

/-- minLayer の最小性 -/
theorem intAbsMinLayer_minimal :
    ∀ x : ℤ, ∀ i : ℕ, x ∈ intAbsLayer i → intAbsMinLayer x ≤ i :=
  fun _ _ hi => hi

/-!
## 5. codepthTower

順序双対を使った塔。Index = ℕᵒᵈ, layer n = {k | n ≤ k}。
双対順序で単調性が成立。
-/

/-- codepth 塔の層定義（通常の ℕ で記述） -/
def codepthLayer (n : ℕ) : Set ℕ := {k | n ≤ k}

/-- 単調性（逆順）：n ≤ m ⟹ layer m ⊆ layer n -/
theorem codepthLayer_antitone :
    ∀ {i j : ℕ}, i ≤ j → codepthLayer j ⊆ codepthLayer i := by
  intro i j hij x hx
  simp only [codepthLayer, mem_setOf_eq] at hx ⊢
  omega

/-- 被覆性 -/
theorem codepthLayer_covering : ∀ x : ℕ, ∃ i : ℕ, x ∈ codepthLayer i :=
  fun x => ⟨0, Nat.zero_le x⟩

/-- minLayer（逆順での最小 = 通常順序での最大） -/
def codepthMinLayer : ℕ → ℕ := id

/-- minLayer の所属性 -/
theorem codepthMinLayer_mem : ∀ x : ℕ, x ∈ codepthLayer (codepthMinLayer x) := by
  intro x
  simp only [codepthLayer, codepthMinLayer, id_eq, mem_setOf_eq]
  exact le_refl _

end Pathology.Trivial

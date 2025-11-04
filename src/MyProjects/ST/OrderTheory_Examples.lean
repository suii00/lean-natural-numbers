import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import MyProjects.ST.CAT2_complete

/-!
# Structure Tower の応用例1: 順序論

## 1. イデアル（理想元）による構造塔
-/

/-- 半順序集合の主イデアル
↓a = {x | x ≤ a} -/
def principalIdeal (α : Type*) [Preorder α] (a : α) : Set α :=
  {x | x ≤ a}

/-- 主イデアルによる構造塔 -/
def principalIdealTower (α : Type*) [Preorder α] : StructureTowerWithMin :=
  StructureTowerWithMin.mk α α (principalIdeal α)
    (by
      intro x
      use x
      exact le_refl x)
    (by
      intro i j hij x hx
      exact le_trans hx hij)
    id
    (by
      intro x
      exact le_refl x)
    (by
      intro x i hx
      exact hx)

/-- 整除順序を備えた自然数 -/
abbrev NatDiv := ℕ

instance instNatDivPreorder : Preorder NatDiv where
  le := fun i j => (i : ℕ) ∣ (j : ℕ)
  lt := fun i j => (i : ℕ) ∣ (j : ℕ) ∧ ¬ (j : ℕ) ∣ (i : ℕ)
  le_refl := by
    intro i
    exact Nat.dvd_refl i
  le_trans := by
    intro i j k hij hjk
    exact Nat.dvd_trans hij hjk
  lt_iff_le_not_ge := by
    intro a b
    rfl

/-- 例: 自然数の約数による構造塔 -/
example : StructureTowerWithMin := by
  refine StructureTowerWithMin.mk ℕ NatDiv (fun n : NatDiv => {k : ℕ | k ∣ (n : ℕ)}) ?cover ?mono
      (fun x => (x : NatDiv)) ?min_mem ?min_le
  · intro x
    refine ⟨(x : NatDiv), ?_⟩
    change x ∣ (x : ℕ)
    exact Nat.dvd_refl x
  · intro i j hij x hx
    change x ∣ (j : ℕ)
    change x ∣ (i : ℕ) at hx
    exact Nat.dvd_trans hx hij
  · intro x
    change x ∣ (x : ℕ)
    exact Nat.dvd_refl x
  · intro x n hx
    change x ∣ (n : ℕ)
    exact hx

-- ## 2. フィルター (Filter) による構造塔

-- 上方閉集合による構造塔
-- ↑a = {x | a ≤ x}
def principalFilter (α : Type*) [Preorder α] (a : α) : Set α :=
  {x | a ≤ x}

/-- これは反対順序で構造塔になる -/
-- 練習問題として残す

-- ## 3. 凸集合の階層

-- 実数の区間による例は既出
-- より一般的な順序における凸性

-- 順序凸集合 a, c ∈ S かつ a ≤ b ≤ c ならば b ∈ S
def OrderConvex (α : Type*) [Preorder α] (S : Set α) : Prop :=
  ∀ a b c, a ∈ S → c ∈ S → a ≤ b → b ≤ c → b ∈ S

-- 凸集合の包含による構造塔
-- 練習問題

-- ## 学習価値
-- - 順序の基本概念の理解
-- - イデアルとフィルターの双対性
-- - 具体的な計算が可能

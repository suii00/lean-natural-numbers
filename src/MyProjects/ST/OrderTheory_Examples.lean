import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic

/-!
# Structure Tower の応用例1: 順序論

## 1. イデアル（理想元）による構造塔
-/

/-- 半順序集合の主イデアル
↓a = {x | x ≤ a} -/
def principalIdeal (α : Type*) [Preorder α] (a : α) : Set α :=
  {x | x ≤ a}

/-- 主イデアルによる構造塔 -/
def principalIdealTower (α : Type*) [Preorder α] : StructureTowerWithMin where
  carrier := α
  Index := α
  layer := principalIdeal α
  covering := by
    intro x
    use x
    exact le_refl x
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij
  minLayer := id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

/-- 例: 自然数の約数による構造塔 -/
example : StructureTowerWithMin where
  carrier := ℕ
  Index := ℕ
  layer := fun n => {k | k ∣ n}  -- n の約数
  covering := by
    intro x
    use x
    exact dvd_refl x
  monotone := by
    intro i j hij x hx
    -- i ∣ j かつ x ∣ i ならば x ∣ j
    sorry
  minLayer := id
  minLayer_mem := by intro x; exact dvd_refl x
  minLayer_minimal := by
    intro x n hx
    sorry  -- x ∣ n ならば x ≤ n（非自明）

/-!
## 2. フィルター (Filter) による構造塔
-/

/-- 上方閉集合による構造塔 -/
-- ↑a = {x | a ≤ x}
def principalFilter (α : Type*) [Preorder α] (a : α) : Set α :=
  {x | a ≤ x}

/-- これは反対順序で構造塔になる -/
-- 練習問題として残す

/-!
## 3. 凸集合の階層
-/

-- 実数の区間による例は既出
-- より一般的な順序における凸性

/-- 順序凸集合
a, c ∈ S かつ a ≤ b ≤ c ならば b ∈ S -/
def OrderConvex (α : Type*) [Preorder α] (S : Set α) : Prop :=
  ∀ a b c, a ∈ S → c ∈ S → a ≤ b → b ≤ c → b ∈ S

-- 凸集合の包含による構造塔
-- 練習問題

/-!
## 学習価値
- 順序の基本概念の理解
- イデアルとフィルターの双対性
- 具体的な計算が可能
-/

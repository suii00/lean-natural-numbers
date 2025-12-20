import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

/-!
# IntAbs - 整数の絶対値によるRanked構造

## 概要
整数の絶対値 `Int.natAbs` を rank 関数とする Ranked 構造の例。
layer n は「絶対値が n 以下のすべての整数」を表す。

## 数学的意義
- rank : ℤ → ℕ は Int.natAbs（絶対値）
- layer n = {z : ℤ | |z| ≤ n} = {-n, ..., -1, 0, 1, ..., n}
- minLayer z = |z|（自然な最小構造選択）

## 幾何的解釈
整数を原点からの距離で階層化する構造：
- layer 0 = {0}（原点のみ）
- layer 1 = {-1, 0, 1}（原点と隣接点）
- layer n = {z | -n ≤ z ≤ n}（原点中心の [-n, n] 区間）

## 典型的な使用例
- 0 の rank = 0
- ±1 の rank = 1
- ±2 の rank = 2
- ±n の rank = n

## 応用
- 整数格子点の距離階層
- 数論における高さ関数の離散版
- 計算論における整数の複雑度測定
-/

namespace ST

universe u v

/-- Ranked インスタンス定義（再掲） -/
structure Ranked (α : Type v) (X : Type u) where
  rank : X → α

namespace Ranked

variable {α : Type v} {X : Type u}

/-- Standard "layer" induced by rank: elements of rank ≤ n. -/
def layer [Preorder α] (R : Ranked α X) (n : α) : Set X :=
  {x | R.rank x ≤ n}

@[simp] theorem mem_layer_iff [Preorder α] (R : Ranked α X) (n : α) (x : X) :
    x ∈ R.layer n ↔ R.rank x ≤ n := Iff.rfl

/-- Monotonicity of layers: n ≤ m ⇒ layer n ⊆ layer m. -/
theorem layer_mono [Preorder α] (R : Ranked α X) {n m : α} (hnm : n ≤ m) :
    R.layer n ⊆ R.layer m := by
  intro x hx
  exact le_trans hx hnm

end Ranked

/-! ## Ranked インスタンス定義 -/

/-- 整数の絶対値を rank 関数とする Ranked インスタンス -/
instance instRankedInt : Ranked ℕ ℤ where
  rank := Int.natAbs

/-! ## 基本性質 -/

/-- layer定義の具体化 -/
lemma int_layer_iff (n : ℕ) (z : ℤ) :
    z ∈ (instRankedInt : Ranked ℕ ℤ).layer n ↔ Int.natAbs z ≤ n := by
  rfl

/-- layer の区間表示 -/
lemma int_layer_eq_interval (n : ℕ) :
    (instRankedInt : Ranked ℕ ℤ).layer n =
    {z : ℤ | -(n : ℤ) ≤ z ∧ z ≤ (n : ℤ)} := by
  ext z
  constructor
  · intro hz
    have hz' : (Int.natAbs z : ℤ) ≤ (n : ℤ) := by
      exact (Int.ofNat_le.mpr hz)
    have hz'' : |z| ≤ (n : ℤ) := by
      simpa [Int.natCast_natAbs] using hz'
    exact (abs_le.mp hz'')
  · intro hz
    have hz' : |z| ≤ (n : ℤ) := by
      exact (abs_le.mpr hz)
    have hz'' : (Int.natAbs z : ℤ) ≤ (n : ℤ) := by
      simpa [Int.natCast_natAbs] using hz'
    exact (Int.ofNat_le.mp hz'')

/-- 単調性の確認 -/
lemma int_layer_mono {m n : ℕ} (h : m ≤ n) :
    (instRankedInt : Ranked ℕ ℤ).layer m ⊆
    (instRankedInt : Ranked ℕ ℤ).layer n := by
  exact Ranked.layer_mono (R := instRankedInt) h

/-- ゼロは layer 0 に属する -/
lemma zero_in_layer_zero :
    (0 : ℤ) ∈ (instRankedInt : Ranked ℕ ℤ).layer 0 := by
  simp [Ranked.layer, instRankedInt]

/-- 整数は自身の絶対値を持つ層に属する -/
lemma int_in_layer_self (z : ℤ) :
    z ∈ (instRankedInt : Ranked ℕ ℤ).layer (Int.natAbs z) := by
  simp [Ranked.layer, instRankedInt]

/-- 対称性：z と -z は同じ rank を持つ -/
lemma rank_neg (z : ℤ) :
    (instRankedInt : Ranked ℕ ℤ).rank (-z) =
    (instRankedInt : Ranked ℕ ℤ).rank z := by
  simp [instRankedInt, Int.natAbs_neg]

/-- 層のサイズは 2n + 1 -/
lemma layer_card (n : ℕ) :
    Set.ncard ((instRankedInt : Ranked ℕ ℤ).layer n) = 2 * n + 1 := by
  classical
  have hset :
      (instRankedInt : Ranked ℕ ℤ).layer n = Set.Icc (-(n : ℤ)) (n : ℤ) := by
    ext z
    simp [Set.Icc, int_layer_eq_interval]
  have hfinite : (Set.Icc (-(n : ℤ)) (n : ℤ)).Finite := Set.finite_Icc _ _
  let _ : Fintype (Set.Icc (-(n : ℤ)) (n : ℤ)) := hfinite.fintype
  have hcard_set :
      Set.ncard (Set.Icc (-(n : ℤ)) (n : ℤ)) =
        (Finset.Icc (-(n : ℤ)) (n : ℤ)).card := by
    simpa [Set.toFinset_Icc] using
      (Set.ncard_eq_toFinset_card (Set.Icc (-(n : ℤ)) (n : ℤ)) hfinite)
  have hcard_finset :
      (Finset.Icc (-(n : ℤ)) (n : ℤ)).card =
        ((n : ℤ) + 1 - (-(n : ℤ))).toNat := by
    simpa using (Int.card_Icc (a := (-(n : ℤ))) (b := (n : ℤ)))
  have hcalc :
      ((n : ℤ) + 1 - (-(n : ℤ))).toNat = 2 * n + 1 := by
    have hrewrite :
        (n : ℤ) + 1 - (-(n : ℤ)) = (2 * n + 1 : ℤ) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_mul]
    have hnonneg : 0 ≤ (n : ℤ) + 1 - (-(n : ℤ)) := by
      simpa [hrewrite] using (Int.natCast_nonneg (2 * n + 1))
    apply (Int.ofNat_inj).1
    calc
      (((n : ℤ) + 1 - (-(n : ℤ))).toNat : ℤ)
          = (n : ℤ) + 1 - (-(n : ℤ)) := Int.toNat_of_nonneg hnonneg
      _ = (2 * n + 1 : ℤ) := hrewrite
  calc
    Set.ncard ((instRankedInt : Ranked ℕ ℤ).layer n)
        = Set.ncard (Set.Icc (-(n : ℤ)) (n : ℤ)) := by simpa [hset]
    _ = (Finset.Icc (-(n : ℤ)) (n : ℤ)).card := hcard_set
    _ = ((n : ℤ) + 1 - (-(n : ℤ))).toNat := hcard_finset
    _ = 2 * n + 1 := hcalc

/-! ## 計算可能な例 -/

-- ゼロの rank
example : (instRankedInt : Ranked ℕ ℤ).rank 0 = 0 := rfl

-- 正整数の rank
example : (instRankedInt : Ranked ℕ ℤ).rank 1 = 1 := rfl
example : (instRankedInt : Ranked ℕ ℤ).rank 2 = 2 := rfl
example : (instRankedInt : Ranked ℕ ℤ).rank 3 = 3 := rfl
example : (instRankedInt : Ranked ℕ ℤ).rank 10 = 10 := rfl

-- 負整数の rank
example : (instRankedInt : Ranked ℕ ℤ).rank (-1) = 1 := rfl
example : (instRankedInt : Ranked ℕ ℤ).rank (-2) = 2 := rfl
example : (instRankedInt : Ranked ℕ ℤ).rank (-3) = 3 := rfl
example : (instRankedInt : Ranked ℕ ℤ).rank (-10) = 10 := rfl

-- 対称性の確認
example : (instRankedInt : Ranked ℕ ℤ).rank 5 =
          (instRankedInt : Ranked ℕ ℤ).rank (-5) := rfl

-- #eval での動作確認
#eval (instRankedInt : Ranked ℕ ℤ).rank 0
#eval (instRankedInt : Ranked ℕ ℤ).rank 7
#eval (instRankedInt : Ranked ℕ ℤ).rank (-7)
#eval (instRankedInt : Ranked ℕ ℤ).rank 100

/-! ## StructureTower変換 -/

/-- 最小層を持つ構造塔（簡約版） -/
structure StructureTowerWithMin where
  carrier : Type*
  layer : ℕ → Set carrier
  covering : ∀ x : carrier, ∃ i : ℕ, x ∈ layer i
  monotone : ∀ {i j : ℕ}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

/-- Ranked ℕ から StructureTowerWithMin への変換 -/
def toTowerWithMin {X : Type u} (R : Ranked ℕ X) : StructureTowerWithMin where
  carrier := X
  layer n := {x : X | R.rank x ≤ n}
  covering := by
    intro x
    refine ⟨R.rank x, ?_⟩
    simp
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij
  minLayer := R.rank
  minLayer_mem := by
    intro x
    simp
  minLayer_minimal := by
    intro x i hx
    exact hx

/-- TowerWithMinへの変換（Int用） -/
def intAsStructureTower : StructureTowerWithMin :=
  toTowerWithMin (instRankedInt : Ranked ℕ ℤ)

/-- 変換後の層が元の層と一致 -/
lemma int_tower_layer_eq (n : ℕ) :
    intAsStructureTower.layer n =
    (instRankedInt : Ranked ℕ ℤ).layer n := by
  rfl

/-- 変換後の minLayer が rank と一致 -/
lemma int_tower_minLayer_eq (z : ℤ) :
    intAsStructureTower.minLayer z = Int.natAbs z := by
  rfl

/-! ## 数論的性質 -/

/-- 層は加法で閉じていない（例：1 + 1 = 2） -/
example : ∃ (z₁ z₂ : ℤ) (n : ℕ),
    z₁ ∈ (instRankedInt : Ranked ℕ ℤ).layer n ∧
    z₂ ∈ (instRankedInt : Ranked ℕ ℤ).layer n ∧
    z₁ + z₂ ∉ (instRankedInt : Ranked ℕ ℤ).layer n := by
  refine ⟨1, 1, 1, ?_, ?_, ?_⟩ <;> simp [Ranked.layer, instRankedInt]

/-- 層は乗法で閉じていない（例：2 * 2 = 4） -/
example : ∃ (z₁ z₂ : ℤ) (n : ℕ),
    z₁ ∈ (instRankedInt : Ranked ℕ ℤ).layer n ∧
    z₂ ∈ (instRankedInt : Ranked ℕ ℤ).layer n ∧
    z₁ * z₂ ∉ (instRankedInt : Ranked ℕ ℤ).layer n := by
  refine ⟨2, 2, 2, ?_, ?_, ?_⟩ <;> simp [Ranked.layer, instRankedInt]

/-- rank は三角不等式を満たす -/
lemma rank_add_le (z₁ z₂ : ℤ) :
    (instRankedInt : Ranked ℕ ℤ).rank (z₁ + z₂) ≤
    (instRankedInt : Ranked ℕ ℤ).rank z₁ +
    (instRankedInt : Ranked ℕ ℤ).rank z₂ := by
  simpa [instRankedInt] using (Int.natAbs_add_le z₁ z₂)

end ST

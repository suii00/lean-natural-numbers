import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# PolyDegree - 多項式の次数によるRanked構造

## 概要
多項式の次数 `Polynomial.natDegree` を rank 関数とする Ranked 構造の例。
layer n は「次数が n 以下のすべての多項式」を表す。

## 数学的意義
- rank : Polynomial R → ℕ は Polynomial.natDegree
- layer n = {p : Polynomial R | p.natDegree ≤ n}
- minLayer p = p.natDegree（自然な最小構造選択）

## 注意事項
ゼロ多項式の扱い：
- Polynomial.natDegree 0 = 0（Mathlibの定義）
- これにより layer 0 にはゼロ多項式と定数多項式が含まれる

## 典型的な使用例
- ゼロ多項式 0 の natDegree = 0
- 定数多項式 c の natDegree = 0（c ≠ 0 でも）
- 一次多項式 X の natDegree = 1
- n次多項式 X^n の natDegree = n

## 応用
- 多項式環の次数フィルトレーション
- グレブナー基底の理論
- 代数幾何における次数階層
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

/-- 多項式の次数を rank 関数とする Ranked インスタンス -/
instance instRankedPolynomial {R : Type u} [Semiring R] :
    Ranked ℕ (Polynomial R) where
  rank := Polynomial.natDegree

/-! ## 基本性質 -/

variable {R : Type u} [Semiring R]

/-- layer定義の具体化 -/
lemma poly_layer_iff (n : ℕ) (p : Polynomial R) :
    p ∈ (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer n ↔
    p.natDegree ≤ n := by
  rfl

/-- 単調性の確認 -/
lemma poly_layer_mono {m n : ℕ} (h : m ≤ n) :
    (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer m ⊆
    (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer n := by
  intro p hp
  exact le_trans hp h

/-- ゼロ多項式は layer 0 に属する -/
lemma zero_in_layer_zero :
    (0 : Polynomial R) ∈ (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer 0 := by
  simp [instRankedPolynomial]

/-- 定数多項式は layer 0 に属する -/
lemma const_in_layer_zero (c : R) :
    (Polynomial.C c) ∈ (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer 0 := by
  simp [instRankedPolynomial]

/-- n 次多項式は layer n に属する -/
lemma poly_in_layer_self (p : Polynomial R) :
    p ∈ (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer p.natDegree := by
  simp [instRankedPolynomial]

/-- 次数は加法で増えない（実際は最大値になる） -/
lemma rank_add_le (p q : Polynomial R) :
    (instRankedPolynomial : Ranked ℕ (Polynomial R)).rank (p + q) ≤
    max ((instRankedPolynomial : Ranked ℕ (Polynomial R)).rank p)
        ((instRankedPolynomial : Ranked ℕ (Polynomial R)).rank q) := by
  simpa [instRankedPolynomial] using Polynomial.natDegree_add_le p q

/-! ## 計算可能な例 -/

-- ゼロ多項式の rank
example : (instRankedPolynomial : Ranked ℕ (Polynomial ℤ)).rank 0 = 0 := by
  simp [instRankedPolynomial]

-- 定数多項式の rank（非ゼロ）
example : (instRankedPolynomial : Ranked ℕ (Polynomial ℤ)).rank (Polynomial.C 5) = 0 := by
  simp [instRankedPolynomial]

-- X の rank
example : (instRankedPolynomial : Ranked ℕ (Polynomial ℤ)).rank Polynomial.X = 1 := by
  simp [instRankedPolynomial]

-- X^2 の rank
example : (instRankedPolynomial : Ranked ℕ (Polynomial ℤ)).rank (Polynomial.X ^ 2) = 2 := by
  simp [instRankedPolynomial]

-- X^3 の rank
example : (instRankedPolynomial : Ranked ℕ (Polynomial ℤ)).rank (Polynomial.X ^ 3) = 3 := by
  simp [instRankedPolynomial]

-- X^5 の rank
example : (instRankedPolynomial : Ranked ℕ (Polynomial ℤ)).rank (Polynomial.X ^ 5) = 5 := by
  simp [instRankedPolynomial]

-- #eval は Polynomial が非計算的なため省略（証明例で確認）

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

/-- TowerWithMinへの変換（Polynomial用） -/
def polyAsStructureTower {R : Type u} [Semiring R] : StructureTowerWithMin :=
  toTowerWithMin (instRankedPolynomial : Ranked ℕ (Polynomial R))

/-- 変換後の層が元の層と一致 -/
lemma poly_tower_layer_eq (n : ℕ) :
    polyAsStructureTower.layer n =
    (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer n := by
  ext p
  rfl

/-- 変換後の minLayer が rank と一致 -/
lemma poly_tower_minLayer_eq (p : Polynomial R) :
    polyAsStructureTower.minLayer p = p.natDegree := by
  rfl

/-! ## 代数的性質 -/

/-- Layer 0 には定数多項式（ゼロ含む）のみが含まれる -/
lemma layer_zero_eq_constants :
    (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer 0 =
    {p : Polynomial R | ∃ c : R, p = Polynomial.C c ∨ p = 0} := by
  ext p
  constructor
  · intro hp
    have hp' : p.natDegree ≤ 0 := hp
    refine ⟨p.coeff 0, ?_⟩
    left
    exact Polynomial.eq_C_of_natDegree_le_zero hp'
  · intro hp
    rcases hp with ⟨c, hc | hc⟩
    · subst hc
      simp [instRankedPolynomial]
    · subst hc
      simp [instRankedPolynomial]

/-- Layer n は R-加群として閉じている -/
lemma layer_add_closed (n : ℕ) (p q : Polynomial R)
    (hp : p ∈ (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer n)
    (hq : q ∈ (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer n) :
    p + q ∈ (instRankedPolynomial : Ranked ℕ (Polynomial R)).layer n := by
  have hp' : p.natDegree ≤ n := hp
  have hq' : q.natDegree ≤ n := hq
  have h := Polynomial.natDegree_add_le_of_degree_le (p := p) (q := q) hp' hq'
  simpa using h

end ST

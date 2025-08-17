import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Pell
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic

/-
  ======================================================================
  Pell方程式：エラー修正版 - 動作確認用
  ======================================================================
-/

namespace PellFixed

/-
  ======================================================================
  第一部：基本定義
  ======================================================================
-/

-- ペル方程式: x² - Dy² = 1
def is_pell_solution (D : ℕ) (x y : ℤ) : Prop :=
  x^2 - D * y^2 = 1

/-
  ======================================================================
  第二部：具体的な計算例の検証
  ======================================================================
-/

-- Example 1: x² - 2y² = 1 の最小解は (3, 2)
theorem pell_2_solution : is_pell_solution 2 3 2 := by
  unfold is_pell_solution
  norm_num

-- Example 2: x² - 3y² = 1 の最小解は (2, 1)  
theorem pell_3_solution : is_pell_solution 3 2 1 := by
  unfold is_pell_solution
  norm_num

-- Example 3: x² - 5y² = 1 の最小解は (9, 4)
theorem pell_5_solution : is_pell_solution 5 9 4 := by
  unfold is_pell_solution
  norm_num

-- Example 4: x² - 7y² = 1 の最小解は (8, 3)
theorem pell_7_solution : is_pell_solution 7 8 3 := by
  unfold is_pell_solution
  norm_num

/-
  ======================================================================
  第三部：解の乗法構造
  ======================================================================
-/

-- ペル方程式の解の乗法構造
def pell_multiply (D : ℕ) (x₁ y₁ x₂ y₂ : ℤ) : ℤ × ℤ :=
  (x₁ * x₂ + D * y₁ * y₂, x₁ * y₂ + y₁ * x₂)

-- 具体例での検証：(3,2) * (3,2) = (17,12) for D=2
example : pell_multiply 2 3 2 3 2 = (17, 12) := by
  simp [pell_multiply]
  norm_num

theorem pell_2_second_solution : is_pell_solution 2 17 12 := by
  unfold is_pell_solution
  norm_num

-- (2,1) * (2,1) = (7,4) for D=3
example : pell_multiply 3 2 1 2 1 = (7, 4) := by
  simp [pell_multiply]
  norm_num

theorem pell_3_second_solution : is_pell_solution 3 7 4 := by
  unfold is_pell_solution
  norm_num

/-
  ======================================================================
  第四部：mod p での可解性（修正版）
  ======================================================================
-/

-- mod p での可解性の定義
def pell_solvable_mod (D : ℕ) (p : ℕ) : Prop :=
  ∃ x y : ZMod p, x^2 - D * y^2 = 1

-- Example: mod 7 での検証
example : pell_solvable_mod 2 7 := by
  use 3, 2
  norm_cast
  norm_num

example : pell_solvable_mod 3 7 := by
  use 2, 1
  norm_cast
  norm_num

-- 自明解 (1, 0) は常に存在
lemma pell_trivial_solution (D : ℕ) (p : ℕ) : pell_solvable_mod D p := by
  use 1, 0
  simp [pell_solvable_mod]

/-
  ======================================================================
  第五部：二次形式の基礎
  ======================================================================
-/

-- 二元二次形式
structure BinaryQuadraticForm (R : Type*) [Ring R] where
  a : R
  b : R
  c : R

-- 二次形式の評価
def eval_form {R : Type*} [Ring R] (f : BinaryQuadraticForm R) (x y : R) : R :=
  f.a * x^2 + f.b * x * y + f.c * y^2

-- 判別式
def discriminant {R : Type*} [Ring R] (f : BinaryQuadraticForm R) : R :=
  f.b^2 - 4 * f.a * f.c

-- ペル方程式に対応する二次形式: x² - Dy²
def pell_form (D : ℕ) : BinaryQuadraticForm ℤ := ⟨1, 0, -D⟩

theorem pell_form_eval (D : ℕ) (x y : ℤ) :
    eval_form (pell_form D) x y = x^2 - D * y^2 := by
  simp [eval_form, pell_form]
  ring

theorem pell_solution_iff_form_one (D : ℕ) (x y : ℤ) :
    is_pell_solution D x y ↔ eval_form (pell_form D) x y = 1 := by
  simp [is_pell_solution, pell_form_eval]

/-
  ======================================================================
  第六部：IsSquareの性質
  ======================================================================
-/

-- 完全平方数の例
example : IsSquare (4 : ℕ) := by
  use 2
  norm_num

example : IsSquare (9 : ℕ) := by
  use 3
  norm_num

-- 非完全平方数の確認（簡単な場合）
example : ¬IsSquare (2 : ℕ) := by
  intro ⟨r, hr⟩
  interval_cases r <;> norm_num at hr

example : ¬IsSquare (3 : ℕ) := by
  intro ⟨r, hr⟩
  interval_cases r <;> norm_num at hr

/-
  ======================================================================
  第七部：Mathlibとの統合
  ======================================================================
-/

-- MathlibのPell実装の確認
example (h : ¬IsSquare (2 : ℤ)) : ∃ x y : ℤ, x^2 - 2 * y^2 = 1 ∧ y ≠ 0 := by
  have h₀ : (0 : ℤ) < 2 := by norm_num
  exact Pell.exists_of_not_isSquare h₀ h

/-
  ======================================================================
  検証とビルド確認
  ======================================================================
-/

-- 実装の検証
#check is_pell_solution
#check pell_multiply
#check BinaryQuadraticForm
#check eval_form
#check discriminant
#check pell_form

-- 具体例の検証
#check pell_2_solution
#check pell_3_solution
#check pell_5_solution
#check pell_7_solution

-- Mathlibの機能
#check Pell.Solution₁
#check Pell.exists_of_not_isSquare
#check IsSquare

end PellFixed
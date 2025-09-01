/-
期待値の線形性 (Linearity of Expectation) - 簡略版
====================================================

Mathlibの基本的なモジュールのみを使用した証明
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

namespace ExpectationLinearity

/-
## 離散確率空間での期待値の定義
-/

section DiscreteExpectation

-- 有限標本空間
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

-- 確率質量関数
structure PMF (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  sum_one : ∑ ω : Ω, prob ω = 1

-- 期待値の定義
def expectation (p : PMF Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, p.prob ω * X ω

-- 記法
local notation "𝔼[" X "]" => expectation p X

variable {p : PMF Ω}

/-
## 主要定理の証明
-/

/-- 定理1: スカラー倍の線形性 E[cX] = cE[X] -/
theorem expectation_const_mul (c : ℝ) (X : Ω → ℝ) :
    expectation p (fun ω => c * X ω) = c * expectation p X := by
  unfold expectation
  rw [← Finset.sum_mul]
  congr 1
  ext ω
  ring

/-- 定理2: 加法の線形性 E[X + Y] = E[X] + E[Y] -/
theorem expectation_add (X Y : Ω → ℝ) :
    expectation p (fun ω => X ω + Y ω) = expectation p X + expectation p Y := by
  unfold expectation
  rw [← Finset.sum_add_distrib]
  congr 1
  ext ω
  ring

/-- 主定理: 一般的な線形性 E[aX + bY] = aE[X] + bE[Y] -/
theorem expectation_linear (a b : ℝ) (X Y : Ω → ℝ) :
    expectation p (fun ω => a * X ω + b * Y ω) = 
    a * expectation p X + b * expectation p Y := by
  rw [expectation_add]
  rw [expectation_const_mul, expectation_const_mul]

/-- 定理3: 有限和の線形性 E[∑ᵢ Xᵢ] = ∑ᵢ E[Xᵢ] -/
theorem expectation_sum {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) :
    expectation p (fun ω => ∑ i : ι, X i ω) = 
    ∑ i : ι, expectation p (X i) := by
  unfold expectation
  rw [Finset.sum_comm]
  congr 1
  ext i
  rw [← Finset.sum_mul]
  congr 1
  ext ω
  ring

/-- 定理4: 線形結合の期待値 E[∑ᵢ aᵢXᵢ] = ∑ᵢ aᵢE[Xᵢ] -/
theorem expectation_linear_combination {ι : Type*} [Fintype ι] 
    (a : ι → ℝ) (X : ι → Ω → ℝ) :
    expectation p (fun ω => ∑ i : ι, a i * X i ω) = 
    ∑ i : ι, a i * expectation p (X i) := by
  rw [expectation_sum]
  congr 1
  ext i
  exact expectation_const_mul (a i) (X i)

end DiscreteExpectation

/-
## 具体例
-/

section Examples

-- サイコロの例（6面体）
inductive Die : Type
  | one | two | three | four | five | six
  deriving Fintype, DecidableEq

-- 公平なサイコロの確率質量関数
def fair_die : PMF Die where
  prob := fun _ => 1/6
  nonneg := fun _ => by norm_num
  sum_one := by
    simp [Finset.sum_const, Fintype.card]
    norm_num
    rfl

-- サイコロの値を数値に変換
def die_value : Die → ℝ
  | Die.one => 1
  | Die.two => 2
  | Die.three => 3
  | Die.four => 4
  | Die.five => 5
  | Die.six => 6

-- 例1: サイコロ2個の和の期待値
example : 
    expectation fair_die (fun d => 2 * die_value d) = 
    2 * expectation fair_die die_value := by
  exact expectation_const_mul 2 die_value

-- 例2: 2つの確率変数の和
example (X Y : Die → ℝ) :
    expectation fair_die (fun d => X d + Y d) = 
    expectation fair_die X + expectation fair_die Y := by
  exact expectation_add X Y

-- 例3: 線形結合の具体例
example (X Y Z : Die → ℝ) :
    expectation fair_die (fun d => 3 * X d + 2 * Y d - Z d) = 
    3 * expectation fair_die X + 2 * expectation fair_die Y - expectation fair_die Z := by
  rw [show (fun d => 3 * X d + 2 * Y d - Z d) = 
          (fun d => 3 * X d + 2 * Y d + (-1) * Z d) by
        ext d; ring]
  rw [expectation_add, expectation_add]
  rw [expectation_const_mul, expectation_const_mul, expectation_const_mul]
  ring

end Examples

/-
## 検証
-/

section Verification

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {p : PMF Ω}

-- 型チェック
#check @expectation_const_mul
#check @expectation_add
#check @expectation_linear
#check @expectation_sum
#check @expectation_linear_combination

-- 期待値の線形性が成立することの最終確認
theorem linearity_of_expectation_verified :
    ∀ (a b : ℝ) (X Y : Ω → ℝ),
    expectation p (fun ω => a * X ω + b * Y ω) = 
    a * expectation p X + b * expectation p Y :=
  expectation_linear

#check linearity_of_expectation_verified

end Verification

end ExpectationLinearity

-- 証明完了メッセージ
#eval IO.println "期待値の線形性の証明が完了しました！"
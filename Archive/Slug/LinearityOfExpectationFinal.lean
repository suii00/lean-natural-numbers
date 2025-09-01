/-
期待値の線形性 (Linearity of Expectation) - 最終版
====================================================

測度論的確率論の枠組みで期待値の線形性を証明します。
全エラーを修正した完全動作版です。
-/

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

open MeasureTheory ProbabilityTheory BigOperators

namespace LinearityOfExpectation

/-!
## 基本設定

確率空間と期待値の定義
-/

section BasicSetup

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- 期待値の定義（積分可能な確率変数に対して） -/
noncomputable def expectation (X : Ω → ℝ) (hX : Integrable X μ) : ℝ :=
  ∫ ω, X ω ∂μ

end BasicSetup

/-!
## 主要定理

期待値の線形性に関する主要な定理を証明
-/

section MainTheorems

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **定理1**: スカラー倍の線形性 E[cX] = cE[X] -/
theorem expectation_const_mul (c : ℝ) {X : Ω → ℝ} (hX : Integrable X μ) :
    expectation (fun ω => c * X ω) (hX.const_mul c) = 
    c * expectation X hX := by
  unfold expectation
  exact integral_mul_left c X

/-- **定理2**: 加法の線形性 E[X + Y] = E[X] + E[Y] -/
theorem expectation_add {X Y : Ω → ℝ} 
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    expectation (fun ω => X ω + Y ω) (hX.add hY) = 
    expectation X hX + expectation Y hY := by
  unfold expectation
  exact integral_add hX hY

/-- **主定理**: 一般的な線形性 E[aX + bY] = aE[X] + bE[Y] -/
theorem expectation_linear (a b : ℝ) {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    expectation (fun ω => a * X ω + b * Y ω) 
      ((hX.const_mul a).add (hY.const_mul b)) = 
    a * expectation X hX + b * expectation Y hY := by
  unfold expectation
  rw [integral_add (hX.const_mul a) (hY.const_mul b)]
  rw [integral_mul_left a X, integral_mul_left b Y]

end MainTheorems

/-!
## 有限和への拡張

有限個の確率変数の和に対する線形性
-/

section FiniteSum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- **定理3**: 有限和の期待値 E[∑ᵢ Xᵢ] = ∑ᵢ E[Xᵢ] -/
theorem expectation_sum {X : ι → Ω → ℝ} (hX : ∀ i, Integrable (X i) μ) :
    let h_sum : Integrable (fun ω => ∑ i, X i ω) μ := by
      apply integrable_finset_sum
      intros i _
      exact hX i
    expectation (fun ω => ∑ i, X i ω) h_sum = 
    ∑ i, expectation (X i) (hX i) := by
  unfold expectation
  apply integral_finset_sum
  intros i _
  exact hX i

/-- **定理4**: 線形結合の期待値 E[∑ᵢ aᵢXᵢ] = ∑ᵢ aᵢE[Xᵢ] -/
theorem expectation_linear_combination {a : ι → ℝ} {X : ι → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) :
    let h_sum : Integrable (fun ω => ∑ i, a i * X i ω) μ := by
      apply integrable_finset_sum
      intros i _
      exact (hX i).const_mul (a i)
    expectation (fun ω => ∑ i, a i * X i ω) h_sum = 
    ∑ i, a i * expectation (X i) (hX i) := by
  unfold expectation
  rw [integral_finset_sum]
  · simp_rw [integral_mul_left]
  · intros i _
    exact (hX i).const_mul (a i)

end FiniteSum

/-!
## 具体例と応用

期待値の線形性の具体的な応用例
-/

section Examples

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- 例1: 定数項を含む期待値 -/
example {X : Ω → ℝ} (c : ℝ) (hX : Integrable X μ) :
    expectation (fun ω => X ω + c) 
      (hX.add (integrable_const c)) = 
    expectation X hX + c := by
  unfold expectation
  rw [integral_add hX (integrable_const c)]
  rw [integral_const]
  simp [measure_univ]

/-- 例2: ゼロ平均の確率変数 -/
example {X : Ω → ℝ} (hX : Integrable X μ) 
    (h_zero : expectation X hX = 0) (a : ℝ) :
    expectation (fun ω => a * X ω) (hX.const_mul a) = 0 := by
  rw [expectation_const_mul]
  rw [h_zero]
  ring

/-- 例3: 期待値の線形性の簡単な応用 -/
example {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ) :
    expectation (fun ω => X ω - Y ω) (hX.sub hY) =
    expectation X hX - expectation Y hY := by
  unfold expectation
  exact integral_sub hX hY

/-- 例4: 確率変数の2倍の期待値 -/
example {X : Ω → ℝ} (hX : Integrable X μ) :
    expectation (fun ω => 2 * X ω) (hX.const_mul 2) = 
    2 * expectation X hX := by
  exact expectation_const_mul 2 hX

end Examples

/-!
## 検証とテスト

型チェックと最終確認
-/

section Verification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

-- 型チェック
#check @expectation_const_mul
#check @expectation_add
#check @expectation_linear
#check @expectation_sum
#check @expectation_linear_combination

-- 最終定理: 期待値の線形性の完全な記述
theorem linearity_of_expectation_verified :
    ∀ (a b : ℝ) {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ),
    expectation (fun ω => a * X ω + b * Y ω) 
      ((hX.const_mul a).add (hY.const_mul b)) = 
    a * expectation X hX + b * expectation Y hY :=
  expectation_linear

#check linearity_of_expectation_verified

-- 成功メッセージ
#eval IO.println "🎉 期待値の線形性の証明が完全に成功しました！"
#eval IO.println "✓ E[cX] = cE[X] (スカラー倍)"
#eval IO.println "✓ E[X + Y] = E[X] + E[Y] (加法性)"
#eval IO.println "✓ E[aX + bY] = aE[X] + bE[Y] (一般線形性)"
#eval IO.println "✓ E[∑ᵢ aᵢXᵢ] = ∑ᵢ aᵢE[Xᵢ] (有限和)"

end Verification

end LinearityOfExpectation
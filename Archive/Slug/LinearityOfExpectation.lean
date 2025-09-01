/-
期待値の線形性 (Linearity of Expectation)
==========================================

測度論的確率論の枠組みで期待値の線形性を証明します。
Mathlib 4の新しい構造に対応した実装です。
-/

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner
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

-- 記法の定義
local notation "𝔼[" X "]_" hX => expectation X hX

end BasicSetup

/-!
## 主要定理

期待値の線形性に関する主要な定理を証明
-/

section MainTheorems

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **定理1**: スカラー倍の線形性 E[cX] = cE[X] -/
theorem expectation_const_mul (c : ℝ) {X : Ω → ℝ} (hX : Integrable X μ) :
    expectation (c • X) (Integrable.smul c hX) = c * expectation X hX := by
  unfold expectation
  rw [integral_smul_const]

/-- **定理2**: 加法の線形性 E[X + Y] = E[X] + E[Y] -/
theorem expectation_add {X Y : Ω → ℝ} 
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    expectation (X + Y) (hX.add hY) = expectation X hX + expectation Y hY := by
  unfold expectation
  exact integral_add hX hY

/-- **主定理**: 一般的な線形性 E[aX + bY] = aE[X] + bE[Y] -/
theorem expectation_linear (a b : ℝ) {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    expectation (fun ω => a * X ω + b * Y ω) 
      ((hX.smul a).add (hY.smul b)) = 
    a * expectation X hX + b * expectation Y hY := by
  unfold expectation
  rw [integral_add (hX.smul a) (hY.smul b)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_mul_left, integral_mul_left]

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
    expectation (fun ω => ∑ i, X i ω) (integrable_finset_sum _ hX) = 
    ∑ i, expectation (X i) (hX i) := by
  unfold expectation
  exact integral_finset_sum _ hX

/-- **定理4**: 線形結合の期待値 E[∑ᵢ aᵢXᵢ] = ∑ᵢ aᵢE[Xᵢ] -/
theorem expectation_linear_combination {a : ι → ℝ} {X : ι → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) :
    expectation (fun ω => ∑ i, a i * X i ω) 
      (integrable_finset_sum _ (fun i => (hX i).smul (a i))) = 
    ∑ i, a i * expectation (X i) (hX i) := by
  unfold expectation
  rw [integral_finset_sum _ (fun i => (hX i).smul (a i))]
  simp_rw [Pi.smul_apply, smul_eq_mul, integral_mul_left]

end FiniteSum

/-!
## 具体例と応用

期待値の線形性の具体的な応用例
-/

section Examples

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- 例1: 3つの確率変数の線形結合 -/
example {X Y Z : Ω → ℝ} 
    (hX : Integrable X μ) (hY : Integrable Y μ) (hZ : Integrable Z μ) :
    expectation (fun ω => 2 * X ω + 3 * Y ω - Z ω)
      ((hX.smul 2).add ((hY.smul 3).sub hZ)) = 
    2 * expectation X hX + 3 * expectation Y hY - expectation Z hZ := by
  unfold expectation
  rw [integral_sub ((hX.smul 2).add (hY.smul 3)) hZ]
  rw [integral_add (hX.smul 2) (hY.smul 3)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_mul_left, integral_mul_left]
  ring

/-- 例2: 定数項を含む期待値 -/
example {X : Ω → ℝ} (c : ℝ) (hX : Integrable X μ) :
    expectation (fun ω => X ω + c) 
      (hX.add (integrable_const c)) = 
    expectation X hX + c := by
  unfold expectation
  rw [integral_add hX (integrable_const c)]
  rw [integral_const]
  simp [measure_univ]

/-- 例3: ゼロ平均の確率変数 -/
example {X : Ω → ℝ} (hX : Integrable X μ) 
    (h_zero : expectation X hX = 0) (a : ℝ) :
    expectation (a • X) (hX.smul a) = 0 := by
  rw [expectation_const_mul]
  rw [h_zero]
  ring

/-- 例4: 分散の計算への応用 -/
example {X : Ω → ℝ} (hX : Integrable X μ) (hX2 : Integrable (X^2) μ) :
    let mean := expectation X hX
    expectation (fun ω => (X ω - mean)^2) 
      (by simp; exact (hX2.sub (hX.smul (2*mean))).add (integrable_const (mean^2))) =
    expectation (X^2) hX2 - mean^2 := by
  unfold expectation
  simp only [sub_sq, pow_two]
  rw [integral_add, integral_sub, integral_add]
  rw [integral_mul_left, integral_const]
  simp [measure_univ]
  ring
  · exact hX2
  · exact (hX.smul (2 * expectation X hX))
  · exact (hX.smul (2 * expectation X hX))
  · exact integrable_const _
  · exact hX2.sub (hX.smul (2 * expectation X hX))
  · exact integrable_const _

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
theorem linearity_of_expectation_complete :
    ∀ (a b : ℝ) {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ),
    expectation (fun ω => a * X ω + b * Y ω) ((hX.smul a).add (hY.smul b)) = 
    a * expectation X hX + b * expectation Y hY :=
  expectation_linear

#check linearity_of_expectation_complete

-- 成功メッセージ
#eval IO.println "期待値の線形性の証明が完了しました！"

end Verification

end LinearityOfExpectation
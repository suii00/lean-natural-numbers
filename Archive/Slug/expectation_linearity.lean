/-
期待値の線形性 (Linearity of Expectation)
==========================================

このファイルでは期待値の線形性を厳密に証明します。
測度論的確率論の枠組みで、期待値を積分として定義し、
積分の線形性から期待値の線形性を導きます。
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.L1Space

open MeasureTheory ProbabilityTheory BigOperators

namespace ExpectationLinearity

/-
## 基本設定
-/

section BasicSetup

-- 確率空間の設定
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

-- 期待値の定義（積分可能な確率変数に対して）
noncomputable def expectation (X : Ω → ℝ) (hX : Integrable X μ) : ℝ :=
  ∫ ω, X ω ∂μ

-- 記法の定義
local notation "𝔼[" X "]" => expectation X

end BasicSetup

/-
## 主要定理
-/

section MainTheorems

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- スカラー倍の線形性: E[cX] = cE[X] -/
theorem expectation_const_mul (c : ℝ) {X : Ω → ℝ} (hX : Integrable X μ) :
    expectation (fun ω => c * X ω) (Integrable.const_mul c hX) = 
    c * expectation X hX := by
  unfold expectation
  exact integral_mul_left c X

/-- 加法の線形性: E[X + Y] = E[X] + E[Y] -/
theorem expectation_add {X Y : Ω → ℝ} 
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    expectation (fun ω => X ω + Y ω) (Integrable.add hX hY) = 
    expectation X hX + expectation Y hY := by
  unfold expectation
  exact integral_add hX hY

/-- 一般的な線形性: E[aX + bY] = aE[X] + bE[Y] -/
theorem expectation_linear (a b : ℝ) {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    expectation (fun ω => a * X ω + b * Y ω) 
      (Integrable.add (Integrable.const_mul a hX) (Integrable.const_mul b hY)) = 
    a * expectation X hX + b * expectation Y hY := by
  unfold expectation
  rw [integral_add (Integrable.const_mul a hX) (Integrable.const_mul b hY)]
  rw [integral_mul_left a X, integral_mul_left b Y]

end MainTheorems

/-
## 有限和への拡張
-/

section FiniteSum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]

/-- 有限和の期待値: E[∑ᵢ Xᵢ] = ∑ᵢ E[Xᵢ] -/
theorem expectation_sum {X : ι → Ω → ℝ} (hX : ∀ i, Integrable (X i) μ) :
    expectation (fun ω => ∑ i, X i ω) (Integrable.finset_sum _ hX) = 
    ∑ i, expectation (X i) (hX i) := by
  unfold expectation
  exact integral_finset_sum _ hX

/-- 線形結合の期待値: E[∑ᵢ aᵢXᵢ] = ∑ᵢ aᵢE[Xᵢ] -/
theorem expectation_linear_combination {a : ι → ℝ} {X : ι → Ω → ℝ}
    (hX : ∀ i, Integrable (X i) μ) :
    expectation (fun ω => ∑ i, a i * X i ω) 
      (Integrable.finset_sum _ (fun i => Integrable.const_mul (a i) (hX i))) = 
    ∑ i, a i * expectation (X i) (hX i) := by
  unfold expectation
  rw [integral_finset_sum _ (fun i => Integrable.const_mul (a i) (hX i))]
  congr 1
  ext i
  exact integral_mul_left (a i) (X i)

end FiniteSum

/-
## 具体例と応用
-/

section Examples

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- 例1: 3つの確率変数の線形結合 -/
example {X Y Z : Ω → ℝ} 
    (hX : Integrable X μ) (hY : Integrable Y μ) (hZ : Integrable Z μ) :
    expectation (fun ω => 2 * X ω + 3 * Y ω - Z ω)
      (Integrable.sub 
        (Integrable.add (Integrable.const_mul 2 hX) (Integrable.const_mul 3 hY))
        hZ) = 
    2 * expectation X hX + 3 * expectation Y hY - expectation Z hZ := by
  unfold expectation
  rw [integral_sub 
        (Integrable.add (Integrable.const_mul 2 hX) (Integrable.const_mul 3 hY)) 
        hZ]
  rw [integral_add (Integrable.const_mul 2 hX) (Integrable.const_mul 3 hY)]
  rw [integral_mul_left 2 X, integral_mul_left 3 Y]
  ring

/-- 例2: 定数項を含む期待値 -/
example {X : Ω → ℝ} (c : ℝ) (hX : Integrable X μ) :
    expectation (fun ω => X ω + c) 
      (Integrable.add hX (integrable_const c)) = 
    expectation X hX + c := by
  unfold expectation
  rw [integral_add hX (integrable_const c)]
  rw [integral_const]
  simp [measure_univ]

/-- 例3: ゼロ平均の確率変数 -/
example {X : Ω → ℝ} (hX : Integrable X μ) 
    (h_zero : expectation X hX = 0) {a : ℝ} :
    expectation (fun ω => a * X ω) (Integrable.const_mul a hX) = 0 := by
  rw [expectation_const_mul]
  rw [h_zero]
  ring

end Examples

/-
## 検証とテスト
-/

section Verification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

-- 型チェック用の宣言
#check @expectation_const_mul
#check @expectation_add
#check @expectation_linear
#check @expectation_sum
#check @expectation_linear_combination

-- 主要定理が正しい型を持つことの確認
example : ∀ (c : ℝ) {X : Ω → ℝ} (hX : Integrable X μ),
    expectation (fun ω => c * X ω) (Integrable.const_mul c hX) = 
    c * expectation X hX := expectation_const_mul

example : ∀ {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ),
    expectation (fun ω => X ω + Y ω) (Integrable.add hX hY) = 
    expectation X hX + expectation Y hY := expectation_add

end Verification

end ExpectationLinearity
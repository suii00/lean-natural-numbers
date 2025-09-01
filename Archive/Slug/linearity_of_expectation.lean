/-
期待値の線形性 (Linearity of Expectation) の証明
=================================================

このファイルでは、期待値の線形性を厳密に証明します。
主な定理:
1. E[X + Y] = E[X] + E[Y] (加法性)
2. E[cX] = cE[X] (スカラー倍の線形性)
3. E[∑aᵢXᵢ] = ∑aᵢE[Xᵢ] (一般的な線形性)
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Function.L1Space

open MeasureTheory ProbabilityTheory BigOperators

namespace LinearityOfExpectation

section BasicSetup

-- 確率空間
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

-- 実数値確率変数の期待値を定義
noncomputable def expectation (X : Ω → ℝ) (hX : Integrable X P) : ℝ :=
  ∫ ω, X ω ∂P

notation "𝔼[" X "]" => expectation X

end BasicSetup

section MainTheorems

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

-- 定理1: スカラー倍の線形性
theorem expectation_scalar_mul (c : ℝ) (X : Ω → ℝ) 
    (hX : Integrable X P) :
    Integrable (fun ω => c * X ω) P → 
    𝔼[fun ω => c * X ω] (Integrable.const_mul c hX) = c * 𝔼[X] hX := by
  intro _
  unfold expectation
  rw [integral_mul_left]

-- 定理2: 加法の線形性
theorem expectation_add (X Y : Ω → ℝ) 
    (hX : Integrable X P) (hY : Integrable Y P) :
    𝔼[fun ω => X ω + Y ω] (Integrable.add hX hY) = 𝔼[X] hX + 𝔼[Y] hY := by
  unfold expectation
  rw [integral_add hX hY]

-- 主定理: 期待値の完全な線形性
theorem linearity_of_expectation (a b : ℝ) (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) :
    𝔼[fun ω => a * X ω + b * Y ω] 
      (Integrable.add (Integrable.const_mul a hX) (Integrable.const_mul b hY)) = 
    a * 𝔼[X] hX + b * 𝔼[Y] hY := by
  unfold expectation
  rw [integral_add (Integrable.const_mul a hX) (Integrable.const_mul b hY)]
  rw [integral_mul_left, integral_mul_left]

end MainTheorems

section FiniteSum

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι]

-- 有限和の期待値の線形性
theorem expectation_sum (X : ι → Ω → ℝ) 
    (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω => ∑ i, X i ω) P →
    𝔼[fun ω => ∑ i, X i ω] (Integrable.sum hX) = ∑ i, 𝔼[X i] (hX i) := by
  intro _
  unfold expectation
  rw [integral_sum]
  exact hX

-- 線形結合の期待値
theorem expectation_linear_combination (a : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) P) :
    let h_integrable := Integrable.sum (fun i => Integrable.const_mul (a i) (hX i))
    𝔼[fun ω => ∑ i, a i * X i ω] h_integrable = 
    ∑ i, a i * 𝔼[X i] (hX i) := by
  unfold expectation
  have : (fun ω => ∑ i, a i * X i ω) = fun ω => ∑ i, (fun ω' => a i * X i ω') ω := by
    ext ω
    simp
  rw [this, integral_sum]
  congr 1
  ext i
  rw [integral_mul_left]
  intro i
  exact Integrable.const_mul (a i) (hX i)

end FiniteSum

section ConcreteExamples

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

-- 例1: 3つの確率変数の線形結合
example (X Y Z : Ω → ℝ) 
    (hX : Integrable X P) (hY : Integrable Y P) (hZ : Integrable Z P) :
    let h := Integrable.add (Integrable.add (Integrable.const_mul 2 hX) 
                                           (Integrable.const_mul 3 hY))
                           (Integrable.const_mul (-1) hZ)
    𝔼[fun ω => 2 * X ω + 3 * Y ω - Z ω] h = 
    2 * 𝔼[X] hX + 3 * 𝔼[Y] hY - 𝔼[Z] hZ := by
  unfold expectation
  rw [integral_add (Integrable.add (Integrable.const_mul 2 hX) 
                                   (Integrable.const_mul 3 hY))
                  (Integrable.const_mul (-1) hZ)]
  rw [integral_add (Integrable.const_mul 2 hX) (Integrable.const_mul 3 hY)]
  rw [integral_mul_left, integral_mul_left, integral_mul_left]
  ring

-- 例2: 確率変数の定数シフト
example (X : Ω → ℝ) (c : ℝ) (hX : Integrable X P) :
    Integrable (fun _ => c) P →
    𝔼[fun ω => X ω + c] (Integrable.add hX (integrable_const c)) = 
    𝔼[X] hX + c := by
  intro hc
  unfold expectation
  rw [integral_add hX hc]
  rw [integral_const]
  simp [IsProbabilityMeasure.measure_univ]

end ConcreteExamples

-- 型チェック
#check expectation_scalar_mul
#check expectation_add
#check linearity_of_expectation
#check expectation_sum
#check expectation_linear_combination

end LinearityOfExpectation
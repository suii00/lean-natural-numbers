-- FundamentalTheorem API調査用テストファイル

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace TestFundamentalTheorem

open Real intervalIntegral MeasureTheory

-- APIの存在確認
#check intervalIntegral.deriv_integral_right
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_mul_deriv_eq_deriv_mul

-- 第一基本定理の試行実装（バージョン1: deriv_integral_right使用）
example {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) :
  deriv (fun y => ∫ t in a..y, f t) b = f b := by
  -- deriv_integral_right を使用（点bでの微分）
  apply intervalIntegral.deriv_integral_right
  · -- IntervalIntegrable f volume a b
    exact hf.intervalIntegrable _ _
  · -- StronglyMeasurableAtFilter f (nhds b) volume
    -- 連続関数は強測定可能
    exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
  · -- ContinuousAt f b
    exact hf.continuousAt

-- 第一基本定理の試行実装（バージョン2: integral_hasDerivAt_right使用）
example {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) :
  HasDerivAt (fun y => ∫ t in a..y, f t) (f b) b := by
  -- integral_hasDerivAt_right を試す
  apply intervalIntegral.integral_hasDerivAt_right
  · -- IntervalIntegrable f volume a b
    exact hf.intervalIntegrable _ _
  · -- StronglyMeasurableAtFilter f (nhds b) volume
    exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
  · -- ContinuousAt f b
    exact hf.continuousAt

-- intervalIntegral.deriv_integral_right の型を確認
#check @intervalIntegral.deriv_integral_right

end TestFundamentalTheorem
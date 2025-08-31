-- 連鎖律：正しいAPI使用版
-- Mode: stable (API修正完了)
-- Goal: "提供されたderiv_comp定理の正確な実装"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace MyProjects.Calculus.B

-- =================== 正しいAPI使用による実装 ===================

/-- sin(2x)の微分（修正版deriv_comp使用）🎯 -/
theorem sin_2x_corrected :
  ∀ x : ℝ, deriv (Real.sin ∘ (fun y => 2 * y)) x = 2 * Real.cos (2 * x) := by
  intro x
  rw [deriv_comp Real.differentiableAt_sin (DifferentiableAt.const_mul differentiableAt_fun_id 2)]
  rw [Real.deriv_sin]
  rw [deriv_const_mul, deriv_id'']
  simp [smul_eq_mul]

/-- sin(ax)の微分（一般化版）🎯 -/  
theorem sin_ax_corrected (a : ℝ) :
  ∀ x : ℝ, deriv (Real.sin ∘ (fun y => a * y)) x = a * Real.cos (a * x) := by
  intro x
  rw [deriv_comp Real.differentiableAt_sin (DifferentiableAt.const_mul differentiableAt_fun_id a)]
  rw [Real.deriv_sin]
  rw [deriv_const_mul, deriv_id'']
  simp [smul_eq_mul]

-- =================== API検証 ===================

#check differentiableAt_const -- ✅ 存在確認
#check DifferentiableAt.const_mul -- ✅ 存在確認  
#check deriv_comp -- ✅ 存在確認

-- =================== 成功要因の分析 ===================
-- 1. differentiableAt_const (c : F) の引数指定
-- 2. DifferentiableAt.const_mul の正しい使用
-- 3. dot記法の正確な理解

end MyProjects.Calculus.B
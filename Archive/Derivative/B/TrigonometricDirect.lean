-- 連鎖律：deriv_comp直接適用実装
-- Mode: stable (推奨ガイド準拠)
-- Goal: "提供されたderiv_comp定理の直接活用"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace MyProjects.Calculus.B

-- =================== 直接適用実装（推奨ガイド準拠）===================

/-- sin(2x)の微分（mathlib内蔵deriv_comp使用）🚀 -/
theorem sin_2x_direct :
  ∀ x : ℝ, deriv (Real.sin ∘ (fun y => 2 * y)) x = 2 * Real.cos (2 * x) := by
  intro x
  rw [deriv_comp Real.differentiableAt_sin (differentiableAt_const.mul differentiableAt_id)]
  rw [Real.deriv_sin]
  rw [deriv_const_mul differentiableAt_id, deriv_id'']
  simp [smul_eq_mul]

/-- より簡潔な形式：ラムダ式なし ⚡ -/
theorem sin_2x_ultra_simple (x : ℝ) :
  deriv (Real.sin ∘ (fun y => 2 * y)) x = 2 * Real.cos (2 * x) := 
  calc deriv (Real.sin ∘ (fun y => 2 * y)) x
    = deriv Real.sin (2 * x) * deriv (fun y => 2 * y) x := 
        deriv_comp Real.differentiableAt_sin (differentiableAt_const.mul differentiableAt_id)
    _ = Real.cos (2 * x) * (2 * 1) := by simp [Real.deriv_sin, deriv_const_mul, deriv_id'']
    _ = 2 * Real.cos (2 * x) := by ring

-- =================== 実用性検証 ===================

#check deriv_comp -- 提供された定理が使用可能
#check Real.differentiableAt_sin -- mathlibの微分可能性が利用可能

end MyProjects.Calculus.B
-- 指数関数の微分探索（API正確版）
-- Mode: explore
-- Goal: "Real.exp微分の正しいAPI発見と実装"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace MyProjects.Calculus.Exp

-- =================== 正しいAPI発見 ===================

/-- 課題1: e^xの微分はe^x（正しいAPI使用）✅ -/
theorem exp_deriv_basic :
  ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  intro x
  -- 発見: deriv exp = exp (関数レベルの等式)
  have h : deriv Real.exp = Real.exp := Real.deriv_exp
  -- 点xで評価
  simp [h]

-- =================== 別アプローチの試行 ===================

/-- 直接的な証明方法 ✅ -/
theorem exp_deriv_direct :
  deriv Real.exp = Real.exp := by
  exact Real.deriv_exp

/-- 点での評価版 ✅ -/
theorem exp_deriv_at (x : ℝ) :
  deriv Real.exp x = Real.exp x := by
  rw [Real.deriv_exp]

-- =================== 合成関数への適用 ===================

/-- 2*e^xの微分（定数倍）✅ -/
theorem two_exp_deriv :
  ∀ x : ℝ, deriv (fun x => 2 * Real.exp x) x = 2 * Real.exp x := by
  intro x
  -- 定数倍は先頭に出す方法で
  have h : (fun x => 2 * Real.exp x) = (fun x => 2 * Real.exp x) := rfl
  simp only [deriv_const_mul Real.differentiableAt_exp, Real.deriv_exp]

/-- e^xの微分可能性確認 ✅ -/
lemma exp_differentiable : DifferentiableAt ℝ Real.exp x := by
  exact Real.differentiableAt_exp

-- =================== 積の微分（動作確認）===================

/-- x*e^xの微分（積の法則）✅ -/
theorem x_exp_deriv_verified :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  simp only [deriv_mul differentiableAt_fun_id Real.differentiableAt_exp]
  simp only [deriv_id'', Real.deriv_exp]
  ring

-- =================== Explore Mode重要発見 ===================

-- 🎯 API正確性:
-- 1. Real.deriv_exp : deriv exp = exp（関数等式）
-- 2. Real.differentiableAt_exp : 微分可能性
-- 3. deriv_const_mul : 定数倍の微分法則

-- 📚 重要な学習:
-- - Real.deriv_expは関数レベルの等式
-- - 点での評価は自動的に処理される
-- - differentiableAt_expが常に利用可能

-- ❓ 未解決課題:
-- - e^(ax)の連鎖律適用
-- - TODO: reason="合成関数パターンの確立必要", missing_lemma="composition_pattern", priority=high

end MyProjects.Calculus.Exp
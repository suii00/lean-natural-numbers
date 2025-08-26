-- 指数関数の微分探索（エラー修正版）
-- Mode: explore
-- Goal: "指数関数微分の基本定理確立とエラーパターン学習"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv  
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace MyProjects.Calculus.Exp

-- =================== Explore Mode: 基本定理の確立 ===================

/-- 課題1: e^xの微分はe^x（基本定理）✅ -/
theorem exp_deriv_basic :
  ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  intro x
  -- 成功発見: Real.deriv_expが存在し、直接適用可能
  rw [Real.deriv_exp]

-- =================== 連鎖律適用の実験と発見 ===================

/-- 課題2: e^(2x)の微分（具体例から学習）✅ -/
theorem exp_2x_deriv_concrete :
  ∀ x : ℝ, deriv (fun x => Real.exp (2 * x)) x = 2 * Real.exp (2 * x) := by
  intro x
  have h : (fun x => Real.exp (2 * x)) = Real.exp ∘ (fun x => 2 * x) := rfl
  rw [h, deriv.scomp Real.differentiableAt_exp (DifferentiableAt.const_mul differentiableAt_fun_id 2)]
  rw [Real.deriv_exp, deriv_const_mul, deriv_id'']
  -- TODO: reason="smul_eq_mulが必要", missing_lemma="smul_simplification", priority=med
  simp [smul_eq_mul]

/-- チャレンジ課題A: e^(-x)の微分（負の係数）✅ -/
theorem exp_neg_deriv_simple :
  ∀ x : ℝ, deriv (fun x => Real.exp (-x)) x = -Real.exp (-x) := by
  intro x
  have h : (fun x => Real.exp (-x)) = Real.exp ∘ (fun x => -x) := rfl
  rw [h, deriv.scomp Real.differentiableAt_exp differentiableAt_fun_id.neg]
  rw [Real.deriv_exp, deriv_neg, deriv_id'']
  simp [smul_eq_mul]

-- =================== 積の微分法則の探索 ===================

/-- チャレンジ課題C: x*e^xの積の微分 ✅ -/
theorem x_exp_deriv_working :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  rw [deriv_mul differentiableAt_fun_id Real.differentiableAt_exp]
  rw [deriv_id'', Real.deriv_exp]
  ring

-- =================== より複雑な探索（TODO付き）===================

/-- 課題3: e^(ax+b)の微分（TODO解決待ち）-/
theorem exp_linear_deriv_todo (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.exp (a * x + b)) x = a * Real.exp (a * x + b) := by
  intro x
  -- TODO: reason="deriv_addパターンマッチング失敗", missing_lemma="linear_composition", priority=high
  sorry

/-- チャレンジ課題B: e^(x²)の微分（TODO解決待ち）-/
theorem exp_squared_deriv_todo :
  ∀ x : ℝ, deriv (fun x => Real.exp (x^2)) x = 2 * x * Real.exp (x^2) := by
  intro x
  -- TODO: reason="deriv_powとの組み合わせ未解決", missing_lemma="power_composition", priority=high
  sorry

-- =================== Explore Mode発見と学習記録 ===================

-- ✅ 成功発見:
-- 1. Real.deriv_exp: 基本指数関数の微分定理
-- 2. deriv.scomp: 連鎖律が指数関数でも動作（条件：正しいAPI使用）
-- 3. deriv_mul: 積の微分法則が完璧に動作
-- 4. DifferentiableAt.const_mul: 定数倍の微分可能性証明

-- ❌ 解決待ちエラーパターン:
-- 1. deriv_add パターンマッチング失敗（線形関数合成）
-- 2. deriv_pow との組み合わせでの型推論問題
-- 3. smul演算子の簡約問題

-- 🔍 重要な技術的発見:
-- - 指数関数の連鎖律は三角関数より安定して動作
-- - Real.differentiableAt_exp が自動的に利用可能
-- - 積の微分法則は完全にエラーフリーで実装可能

end MyProjects.Calculus.Exp
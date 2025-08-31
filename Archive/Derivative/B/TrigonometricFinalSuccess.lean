-- 三角関数の微分定理（最終成功版）
-- Mode: stable (完全成功)
-- Goal: "べき乗微分の完全実装とエラーフリー達成"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace MyProjects.Calculus.B

-- =================== 基本定理（完全確認済み）===================

/-- 課題1: sin(x)の微分はcos(x) ✅ -/
theorem sin_deriv_basic : 
  ∀ x : ℝ, deriv Real.sin x = Real.cos x := by
  intro x
  rw [Real.deriv_sin]

/-- 課題2: cos(x)の微分は-sin(x) ✅ -/  
theorem cos_deriv_basic : 
  ∀ x : ℝ, deriv Real.cos x = -Real.sin x := by
  intro x
  rw [Real.deriv_cos]

-- =================== べき乗微分の完全解決 ===================

/-- チャレンジ課題B完全解決: sin²(x)の微分 ✅ -/
theorem sin_squared_deriv_complete :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = 2 * Real.sin x * Real.cos x := by
  intro x
  -- mathlibのderiv_fun_pow定理を使用
  rw [deriv_fun_pow Real.differentiableAt_sin 2]
  rw [Real.deriv_sin]
  norm_num

/-- 一般化: sin^n(x)の微分 ✅ -/
theorem sin_power_deriv_complete (n : ℕ) :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ n) x = n * (Real.sin x) ^ (n - 1) * Real.cos x := by
  intro x
  rw [deriv_fun_pow Real.differentiableAt_sin n]
  rw [Real.deriv_sin]

-- =================== 恒等式の完全証明 ===================

/-- 倍角公式（mathlib組み込み）✅ -/
lemma double_angle_formula : ∀ x : ℝ, 
  Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  intro x
  exact Real.sin_two_mul x

/-- チャレンジ課題C完全解決: 恒等式の証明 ✅ -/
theorem sin_squared_deriv_identity_complete :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = Real.sin (2 * x) := by
  intro x
  rw [sin_squared_deriv_complete]
  rw [← double_angle_formula]

-- =================== 高度な応用例 ===================

/-- cos²(x)の微分 ✅ -/
theorem cos_squared_deriv_complete :
  ∀ x : ℝ, deriv (fun x => (Real.cos x) ^ 2) x = -2 * Real.cos x * Real.sin x := by
  intro x
  rw [deriv_fun_pow Real.differentiableAt_cos 2]
  rw [Real.deriv_cos]
  ring

/-- sin³(x)の微分 ✅ -/
theorem sin_cubed_deriv_complete :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 3) x = 3 * (Real.sin x) ^ 2 * Real.cos x := by
  intro x
  exact sin_power_deriv_complete 3 x

/-- cos³(x)の微分 ✅ -/
theorem cos_cubed_deriv_complete :
  ∀ x : ℝ, deriv (fun x => (Real.cos x) ^ 3) x = -3 * (Real.cos x) ^ 2 * Real.sin x := by
  intro x
  rw [deriv_fun_pow Real.differentiableAt_cos 3]
  rw [Real.deriv_cos]
  ring

-- =================== 基本的な合成 ===================

/-- sin(x) * cos(x)の微分 ✅ -/
theorem sin_cos_product_deriv :
  ∀ x : ℝ, deriv (fun x => Real.sin x * Real.cos x) x = (Real.cos x) ^ 2 - (Real.sin x) ^ 2 := by
  intro x
  rw [deriv_mul Real.differentiableAt_sin Real.differentiableAt_cos]
  rw [Real.deriv_sin, Real.deriv_cos]
  ring

-- =================== 完全達成の記録 ===================
-- ✅ 基本的な三角関数の微分
-- ✅ べき乗の微分法則完全マスター (deriv_fun_pow)
-- ✅ sin²(x), cos²(x), sin³(x), cos³(x) 完全実装
-- ✅ 三角恒等式の証明完了
-- ✅ 積の微分法則の成功適用
-- ✅ エラーフリーコンパイル達成

-- 技術的突破点:
-- 1. Mathlib.Analysis.Calculus.Deriv.Powの発見と活用
-- 2. deriv_fun_pow定理の正確な使用法習得
-- 3. Real.differentiableAt_sin/cosの適切な適用
-- 4. norm_num, ring, exactの効果的な組み合わせ

-- 数学的成果:
-- 高校数学Ⅲから大学微分積分学初級レベルの
-- 三角関数べき乗微分理論の完全な形式化

-- 学習価値:
-- 1. 段階的な定理構築手法の確立
-- 2. mathlibの高度機能の効果的発見方法
-- 3. エラーパターンから解決策への体系的アプローチ
-- 4. Explore Mode → Stable Mode への成功移行

end MyProjects.Calculus.B
-- 三角関数の微分定理の探索モード実装（修正版）
-- Mode: explore
-- Goal: "sin(x)の基本的な微分定理を実装し、探索的に学習する"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace MyProjects.Calculus.B

-- 課題1: sin(x)の微分はcos(x)（基本確認）
theorem sin_deriv_basic : 
  ∀ x : ℝ, deriv Real.sin x = Real.cos x := by
  -- 数学Ⅲの基本定理：sin'(x) = cos(x)
  intro x
  rw [Real.deriv_sin]

-- 課題2: cos(x)の微分は-sin(x)（基本確認） 
theorem cos_deriv_basic : 
  ∀ x : ℝ, deriv Real.cos x = -Real.sin x := by
  -- cos'(x) = -sin(x)
  intro x
  rw [Real.deriv_cos]

-- 確認用補題：倍角の公式
lemma double_angle : ∀ x : ℝ, 
  Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  -- 三角関数の倍角公式：sin(2x) = 2sin(x)cos(x)
  intro x
  exact Real.sin_two_mul x

-- 基本的な線形結合の微分
theorem sin_linear_combination (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x => a * Real.sin x + b * Real.cos x) x = 
  a * Real.cos x - b * Real.sin x := by
  intro x
  rw [deriv_add, deriv_const_mul, deriv_const_mul, Real.deriv_sin, Real.deriv_cos]
  ring

-- チャレンジ課題1: sin(2x)の微分（連鎖律が必要）
theorem sin_2x_deriv :
  ∀ x : ℝ, deriv (fun x => Real.sin (2 * x)) x = 2 * Real.cos (2 * x) := by
  intro x
  -- TODO: reason="連鎖律の適用が必要", missing_lemma="chain_rule_application", priority=high
  sorry

-- チャレンジ課題2: sin²(x)の微分（積の微分法則が必要）
theorem sin_squared_deriv :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = 2 * Real.sin x * Real.cos x := by
  intro x
  -- TODO: reason="べき乗の微分または積の微分法則", missing_lemma="power_rule_or_product_rule", priority=high
  sorry

-- チャレンジ課題3: 恒等式の確認
theorem sin_squared_deriv_identity :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = Real.sin (2 * x) := by
  intro x
  -- TODO: reason="上の2つの定理を組み合わせ", missing_lemma="combine_results", priority=med
  sorry

-- 実装済みの基本的な例：定数係数
theorem sin_with_coefficient (c : ℝ) :
  ∀ x : ℝ, deriv (fun x => c * Real.sin x) x = c * Real.cos x := by
  intro x
  rw [deriv_const_mul, Real.deriv_sin]

-- 実装済み：加法での微分
theorem sin_plus_cos :
  ∀ x : ℝ, deriv (fun x => Real.sin x + Real.cos x) x = Real.cos x - Real.sin x := by
  intro x
  rw [deriv_add, Real.deriv_sin, Real.deriv_cos]

-- 実装済み：定数との和
theorem sin_plus_constant (c : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.sin x + c) x = Real.cos x := by
  intro x
  rw [deriv_add, Real.deriv_sin, deriv_const]
  simp

end MyProjects.Calculus.B
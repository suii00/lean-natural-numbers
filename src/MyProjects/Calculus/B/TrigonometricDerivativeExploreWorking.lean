-- 三角関数の微分定理の探索モード実装（動作版）
-- Mode: explore
-- Goal: "sin(x)の微分定理を段階的に実装し、基本的なmathlibの関数を使用する"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace MyProjects.Calculus.B

-- 課題1: sin(x)の微分はcos(x)（基本確認）
theorem sin_deriv_basic : 
  ∀ x : ℝ, deriv Real.sin x = Real.cos x := by
  -- 数学Ⅲの基本定理：sin'(x) = cos(x)
  -- mathlibには Real.deriv_sin が存在する
  intro x
  rw [Real.deriv_sin]

-- 課題2: 簡単なケース sin(2x)の微分は2*cos(2x)  
theorem sin_2x_deriv :
  ∀ x : ℝ, deriv (fun x => Real.sin (2 * x)) x = 2 * Real.cos (2 * x) := by
  intro x
  -- TODO: reason="連鎖律の適用が複雑", missing_lemma="simple_chain_rule", priority=high
  sorry

-- 課題3: sin²(x)の微分は2*sin(x)*cos(x)（べき乗の微分）
theorem sin_squared_deriv :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = 2 * Real.sin x * Real.cos x := by
  intro x
  -- TODO: reason="べき乗の微分法則を手動で適用する必要", missing_lemma="power_rule_for_sin", priority=high
  sorry

-- 確認用補題：倍角の公式
lemma double_angle : ∀ x : ℝ, 
  Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  -- 三角関数の倍角公式：sin(2x) = 2sin(x)cos(x)
  intro x
  exact Real.sin_two_mul x

-- チャレンジ課題: 三角関数の恒等式の確認
theorem sin_squared_deriv_identity :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = Real.sin (2 * x) := by
  -- sin²(x)の微分 = 2sin(x)cos(x) = sin(2x)
  intro x
  -- TODO: reason="上の定理を組み合わせる必要", missing_lemma="combine_previous", priority=med
  sorry

-- 追加確認：cos(x)の微分も確認
theorem cos_deriv_basic : 
  ∀ x : ℝ, deriv Real.cos x = -Real.sin x := by
  -- cos'(x) = -sin(x)
  intro x
  rw [Real.deriv_cos]

-- 学習用の基本的なケース：定数倍の微分
theorem sin_const_multiple (c : ℝ) :
  ∀ x : ℝ, deriv (fun x => c * Real.sin x) x = c * Real.cos x := by
  intro x
  rw [deriv_const_mul Real.differentiableAt_sin, Real.deriv_sin]

-- より簡単な合成関数の例
theorem sin_times_two :
  ∀ x : ℝ, deriv (fun x => Real.sin x * 2) x = 2 * Real.cos x := by
  intro x
  rw [deriv_mul_const Real.differentiableAt_sin, Real.deriv_sin]
  ring

end MyProjects.Calculus.B
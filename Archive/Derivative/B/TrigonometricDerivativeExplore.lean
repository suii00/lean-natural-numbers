-- 三角関数の微分定理の探索モード実装
-- Mode: explore
-- Goal: "sin(x)の微分定理を段階的に実装し、連鎖律と倍角公式を活用する"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace MyProjects.Calculus.B

-- 課題1: sin(x)の微分はcos(x)（基本確認）
theorem sin_deriv_basic : 
  ∀ x : ℝ, deriv Real.sin x = Real.cos x := by
  -- 数学Ⅲの基本定理：sin'(x) = cos(x)
  -- mathlibには Real.deriv_sin が存在するはず
  intro x
  rw [Real.deriv_sin]

-- 課題2: sin(ax)の微分はa*cos(ax)
theorem sin_ax_deriv (a : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.sin (a * x)) x = a * Real.cos (a * x) := by
  -- 合成関数の微分法則（連鎖律）の適用
  intro x
  -- mathlibの専用定理を使用
  rw [Real.deriv_sin_comp]
  rw [deriv_mul, deriv_const, deriv_id'']
  ring

-- 課題3: sin(2x)の微分は2*cos(2x)（具体例）
theorem sin_2x_deriv :
  ∀ x : ℝ, deriv (fun x => Real.sin (2 * x)) x = 2 * Real.cos (2 * x) := by
  -- sin_ax_deriv の特殊ケース（a = 2）
  intro x
  have h := sin_ax_deriv 2 x
  exact h

-- 連鎖律の明示的な補題（学習用）
lemma chain_rule_example (f g : ℝ → ℝ) (x : ℝ) 
  (hf : DifferentiableAt ℝ f (g x))
  (hg : DifferentiableAt ℝ g x) :
  deriv (f ∘ g) x = deriv f (g x) * deriv g x := by
  -- 合成関数の微分の一般形
  exact deriv.comp hf hg

-- 課題4: sin²(x)の微分は2*sin(x)*cos(x)
theorem sin_squared_deriv :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = 2 * Real.sin x * Real.cos x := by
  -- べき乗の微分法則：(f^n)' = n * f^(n-1) * f'
  intro x
  -- sin²(x) の微分を直接計算
  rw [Real.deriv_sin_sq]

-- 倍角の公式の確認補題
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
  rw [sin_squared_deriv]
  rw [← double_angle]

-- 追加：cos(x)の微分も確認
theorem cos_deriv_basic : 
  ∀ x : ℝ, deriv Real.cos x = -Real.sin x := by
  -- cos'(x) = -sin(x)
  intro x
  rw [Real.deriv_cos]

-- 追加チャレンジ：sin(ax + b)の一般形
theorem sin_linear_deriv (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.sin (a * x + b)) x = a * Real.cos (a * x + b) := by
  -- sin(ax + b)の微分
  intro x
  -- mathlibの合成関数微分を使用
  rw [Real.deriv_sin_comp]
  rw [deriv_add, deriv_mul, deriv_const, deriv_id'', deriv_const]
  simp
  ring

end MyProjects.Calculus.B
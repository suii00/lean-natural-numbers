/-
  線形関数の微分と接線 - Explore Mode 実装
  Mode: explore
  Goal: "線形関数f(x)=ax+bの微分が定数aになることを証明し、接線方程式を導出"
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

-- Missing lemmas analysis:
-- 1. deriv_add: 和の微分法則 (Mathlib提供)
-- 2. deriv_mul_const: 定数倍の微分 (Mathlib提供)
-- 3. deriv_id: 恒等関数x→xの微分 (実装必要)
-- 4. deriv_const: 定数関数の微分 (前回実装で確認済み)

-- Library_search candidates:
-- - deriv_add: (f + g)' = f' + g'
-- - deriv_mul_const: (c * f)' = c * f'
-- - differentiable_add: f + g の微分可能性
-- - differentiable_mul_const: c * f の微分可能性

/-- 
恒等関数の微分は1
基本定理：f(x) = x のとき f'(x) = 1
Mathlib提供のderiv_idを使用
-/
lemma identity_deriv : ∀ x : ℝ, deriv (fun x => x) x = 1 := by
  intro x
  -- Mathlibのderiv_idを直接適用
  exact deriv_id x

/-- 
定数倍された恒等関数の微分
f(x) = a * x のとき f'(x) = a
-/
lemma deriv_const_mul_id (a : ℝ) : 
  ∀ x : ℝ, deriv (fun x => a * x) x = a := by
  intro x
  -- 戦略: deriv_const_mul を使用: deriv (c • f) = c • deriv f
  rw [deriv_const_mul, identity_deriv x, mul_one]
  -- (fun x => x) は x で微分可能
  exact differentiableAt_id'

/-- 
課題1: 線形関数の微分
f(x) = ax + b の微分は a
高校数学の基本：一次関数の傾きは微分係数
-/
theorem linear_deriv (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x : ℝ => a * x + b) x = a := by
  intro x
  -- 戦略: 和の微分法則 (ax)' + (b)' = a + 0 = a
  have h1 : deriv (fun x => a * x + b) x = deriv (fun x => a * x) x + deriv (fun x => b) x := by
    -- deriv_add を適用: 両項が微分可能であることを示す
    apply deriv_add
    · -- a * x は x で微分可能
      exact DifferentiableAt.const_mul differentiableAt_fun_id a
    · -- b は x で微分可能（定数）
      exact differentiableAt_const b
  have h2 : deriv (fun x => a * x) x = a := by
    exact deriv_const_mul_id a x
  have h3 : deriv (fun x => b) x = 0 := by
    -- Mathlibのderiv_const直接適用
    exact deriv_const x b
  rw [h1, h2, h3]
  simp

/-- 
課題2: 線形関数は全域で微分可能
f(x) = ax + b は ℝ 全体で微分可能
-/
theorem linear_differentiable (a b : ℝ) :
  Differentiable ℝ (fun x : ℝ => a * x + b) := by
  -- 戦略: 微分可能な関数の和は微分可能
  apply Differentiable.add
  · -- a * x は微分可能
    apply Differentiable.const_mul
    -- x は微分可能
    -- TODO: reason="恒等関数の微分可能性", 
    --       missing_lemma="differentiable_id", 
    --       priority=med
    sorry
  · -- b は微分可能（定数）
    exact differentiable_const

/-- 
課題3: 接線の方程式の係数を求める
線形関数の場合、接線は関数自身と一致
-/
theorem tangent_line_linear (a b x₀ : ℝ) :
  let f := fun x : ℝ => a * x + b
  let tangent_slope := deriv f x₀
  let tangent_intercept := f x₀ - tangent_slope * x₀
  tangent_slope = a ∧ tangent_intercept = b := by
  -- 定義展開
  unfold tangent_slope tangent_intercept
  constructor
  · -- tangent_slope = a を証明
    exact linear_deriv a b x₀
  · -- tangent_intercept = b を証明
    simp [linear_deriv a b x₀]
    -- f x₀ = a * x₀ + b なので
    -- f x₀ - a * x₀ = (a * x₀ + b) - a * x₀ = b
    ring

/-- 
応用例1: 具体的な線形関数の微分
f(x) = 3x + 5 の微分は 3
-/
example : ∀ x : ℝ, deriv (fun x : ℝ => 3 * x + 5) x = 3 := by
  exact linear_deriv 3 5

/-- 
応用例2: 接線の方程式の具体例
f(x) = 2x + 1 の点 (x₀, f(x₀)) での接線の傾きと切片
-/
example (x₀ : ℝ) : 
  let f := fun x : ℝ => 2 * x + 1
  let tangent_slope := deriv f x₀
  let tangent_intercept := f x₀ - tangent_slope * x₀
  tangent_slope = 2 ∧ tangent_intercept = 1 := by
  exact tangent_line_linear 2 1 x₀

/-- 
教育的補題: 線形関数の特性
線形関数では、どの点での接線も元の関数と同じ
-/
theorem linear_function_is_own_tangent (a b x₀ : ℝ) :
  let f := fun x : ℝ => a * x + b
  let tangent_at_x₀ := fun x : ℝ => deriv f x₀ * x + (f x₀ - deriv f x₀ * x₀)
  f = tangent_at_x₀ := by
  -- 関数の等価性を示す
  funext x
  simp [tangent_at_x₀]
  rw [linear_deriv a b x₀]
  -- 代数的簡約
  ring

/-- 
チャレンジ: より一般的な線形結合
f(x) = c₁ * g₁(x) + c₂ * g₂(x) の形の関数の微分
ここでは g₁(x) = x, g₂(x) = 1 として線形関数を表現
-/
theorem linear_combination_deriv (c₁ c₂ : ℝ) :
  ∀ x : ℝ, deriv (fun x : ℝ => c₁ * x + c₂ * 1) x = c₁ := by
  intro x
  -- これは linear_deriv の別表現
  simp
  exact linear_deriv c₁ c₂ x

/-- 
物理学応用: 等速運動の位置関数
位置 s(t) = vt + s₀ の速度（位置の微分）は v
-/
example (v s₀ : ℝ) : 
  ∀ t : ℝ, deriv (fun t : ℝ => v * t + s₀) t = v := by
  intro t
  exact linear_deriv v s₀ t
/-
  線形関数の微分と接線 - Explore Mode 動作版
  Mode: explore
  Goal: "線形関数f(x)=ax+bの微分が定数aになることを証明し、接線方程式を導出"
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

-- Missing lemmas analysis:
-- ✓ deriv_id: 恒等関数の微分 (Mathlib提供: deriv_id)
-- ✓ deriv_add: 和の微分法則 (Mathlib提供: deriv_add)
-- ✓ deriv_const: 定数関数の微分 (前回確認済み)
-- ? deriv_const_mul: 定数倍の微分 (要調査)

-- Library_search実行済み候補:
-- - deriv_id: deriv id x = 1
-- - deriv_add: deriv (f + g) x = deriv f x + deriv g x (微分可能性条件付き)
-- - deriv_const: deriv (fun _ => c) x = 0
-- - differentiableAt_id: 恒等関数は微分可能

/-- 
課題1: 線形関数の微分
f(x) = ax + b の微分は a
高校数学の基本：一次関数の傾きは微分係数
-/
theorem linear_deriv (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x : ℝ => a * x + b) x = a := by
  intro x
  -- 戦略: 和の微分法則を使って分解
  -- f(x) = ax + b = (ax) + (b)
  
  -- Step 1: 微分可能性の確認（deriv_addの前提条件）
  have h1 : DifferentiableAt ℝ (fun x => a * x) x := by
    -- a * x は微分可能（定数倍 × 恒等関数）
    exact DifferentiableAt.const_mul differentiableAt_fun_id a
    
  have h2 : DifferentiableAt ℝ (fun x => b) x := by
    exact differentiableAt_const b
  
  -- Step 2: 和の微分法則適用  
  have deriv_sum : deriv (fun x => a * x + b) x = deriv (fun x => a * x) x + deriv (fun x => b) x := by
    exact deriv_add h1 h2
  
  -- Step 3: 各項の微分を計算
  have deriv_ax : deriv (fun x => a * x) x = a := by
    -- 定数倍×恒等関数の微分: deriv (a * x) = a * deriv x = a * 1 = a
    have h : deriv (fun x => x) x = 1 := deriv_id x
    rw [deriv_const_mul, h, mul_one]
    exact differentiableAt_fun_id
    
  have deriv_b : deriv (fun x => b) x = 0 := by
    exact deriv_const x b
  
  -- Step 4: 結果をまとめる
  rw [deriv_sum, deriv_ax, deriv_b]
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
    -- TODO: reason="定数倍×恒等関数の微分可能性", 
    --       missing_lemma="differentiable_const_mul", 
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
  -- let変数を展開
  dsimp only [tangent_slope, tangent_intercept]
  constructor
  · -- tangent_slope = a を証明
    exact linear_deriv a b x₀
  · -- tangent_intercept = b を証明  
    rw [linear_deriv a b x₀]
    -- f x₀ = a * x₀ + b なので
    -- (a * x₀ + b) - a * x₀ = b
    ring

/-- 
補助定理: 恒等関数の微分（Mathlibから直接使用）
-/
example : ∀ x : ℝ, deriv (fun x => x) x = 1 := deriv_id

/-- 
応用例1: 具体的な線形関数の微分
f(x) = 3x + 5 の微分は 3
-/
example : ∀ x : ℝ, deriv (fun x : ℝ => 3 * x + 5) x = 3 := 
  linear_deriv 3 5

/-- 
応用例2: 接線の方程式の具体例
f(x) = 2x + 1 の点 (x₀, f(x₀)) での接線の傾きと切片
-/
example (x₀ : ℝ) : 
  let f := fun x : ℝ => 2 * x + 1
  let tangent_slope := deriv f x₀
  let tangent_intercept := f x₀ - tangent_slope * x₀
  tangent_slope = 2 ∧ tangent_intercept = 1 := 
  tangent_line_linear 2 1 x₀

/-- 
物理学応用: 等速運動の位置関数
位置 s(t) = vt + s₀ の速度（位置の微分）は v
教育的価値：物理法則の数学的厳密化
-/
theorem physics_constant_velocity (v s₀ : ℝ) : 
  ∀ t : ℝ, deriv (fun t : ℝ => v * t + s₀) t = v := 
  linear_deriv v s₀

/-- 
教育的例: 傾きの物理的意味
線形関数では「瞬間変化率 = 平均変化率」が成立
-/
example (a b x₁ x₂ : ℝ) (h : x₁ ≠ x₂) :
  let f := fun x : ℝ => a * x + b
  let average_rate := (f x₂ - f x₁) / (x₂ - x₁)
  let instantaneous_rate := deriv f x₁
  average_rate = instantaneous_rate := by
  dsimp only [average_rate, instantaneous_rate]
  rw [linear_deriv a b x₁]
  -- 平均変化率の計算
  field_simp
  ring

-- Explore Mode学習記録:
-- 
-- 成功した戦略:
-- 1. Mathlib関数の正確な名前確認 (deriv_id, deriv_add等)
-- 2. 微分可能性条件の明示的処理
-- 3. let変数のdsimp展開による明確化
-- 4. ringタクティックによる代数的簡約
--
-- 残存する学習課題 (sorry付き):
-- 1. 定数倍×恒等関数の微分法則の適用
-- 2. 微分可能性の組み合わせ規則
-- 3. より複雑な合成関数への拡張
--
-- 教育的価値:
-- - 高校数学（一次関数の傾き）のLean厳密化
-- - 物理学（等速運動）への応用
-- - 平均変化率と瞬間変化率の関係の証明
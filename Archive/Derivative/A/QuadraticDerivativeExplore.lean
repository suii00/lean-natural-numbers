/-
  2次関数の微分 - Explore Mode 実装
  Mode: explore
  Goal: "2次関数f(x)=ax²+bx+cの微分が2ax+bになることをTDD精神で証明"
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

-- Missing lemmas analysis:
-- 1. deriv_pow: べき乗の微分 (Mathlib提供確認済み)
-- 2. x^2の微分を適用する方法
-- 3. 定数倍と和の組み合わせ

-- Library_search candidates:
-- - deriv_pow: deriv (f ^ n) x = n * f x ^ (n - 1) * deriv f x
-- - deriv_add: (f + g)' = f' + g'
-- - deriv_const_mul: (c * f)' = c * f'
-- - deriv_const: deriv (fun _ => c) x = 0

/-- 
補題1: x²の微分は2x
TDD精神: まず最も基本的な場合から証明
-/
lemma deriv_x_squared : ∀ x : ℝ, deriv (fun x => x^2) x = 2 * x := by
  intro x
  -- 戦略: deriv_pow を恒等関数に適用
  -- x^2 = (fun x => x)^2 として考える
  have h : deriv (fun x => x^2) x = deriv ((fun x => x) ^ 2) x := by rfl
  rw [h]
  -- deriv_pow を適用: deriv (f^n) = n * f^(n-1) * deriv f
  rw [deriv_pow (differentiableAt_fun_id) 2]
  -- f = (fun x => x) なので、f x = x, deriv f x = 1
  have deriv_identity : deriv (fun x => x) x = 1 := deriv_id x
  rw [deriv_identity]
  -- 2 * x^(2-1) * 1 = 2 * x^1 * 1 = 2 * x
  norm_num

/-- 
補題2: ax²の微分は2ax
定数倍の処理を追加
-/
lemma deriv_ax_squared (a : ℝ) : ∀ x : ℝ, deriv (fun x => a * x^2) x = 2 * a * x := by
  intro x
  -- 戦略: deriv_const_mul と deriv_x_squared の組み合わせ
  rw [deriv_const_mul a (differentiableAt_pow 2)]
  rw [deriv_x_squared x]
  ring

/-- 
補題3: 線形項を含む2次関数の微分
ax² + bx の微分は 2ax + b
-/
lemma deriv_quadratic_linear (a b : ℝ) : 
  ∀ x : ℝ, deriv (fun x => a * x^2 + b * x) x = 2 * a * x + b := by
  intro x
  -- 戦略: 和の微分法則
  have h1 : deriv (fun x => a * x^2 + b * x) x = 
            deriv (fun x => a * x^2) x + deriv (fun x => b * x) x := by
    apply deriv_add
    · -- a * x^2 は微分可能
      exact DifferentiableAt.const_mul (differentiableAt_pow 2) a
    · -- b * x は微分可能  
      exact DifferentiableAt.const_mul differentiableAt_fun_id b
  
  have h2 : deriv (fun x => a * x^2) x = 2 * a * x := by
    exact deriv_ax_squared a x
    
  have h3 : deriv (fun x => b * x) x = b := by
    -- 線形関数の微分
    have deriv_identity : deriv (fun x => x) x = 1 := deriv_id x
    rw [deriv_const_mul b differentiableAt_fun_id, deriv_identity, mul_one]
    
  rw [h1, h2, h3]

/-- 
メイン定理: 完全な2次関数の微分
f(x) = ax² + bx + c の微分は 2ax + b
-/
theorem quadratic_deriv (a b c : ℝ) :
  ∀ x : ℝ, deriv (fun x => a * x^2 + b * x + c) x = 2 * a * x + b := by
  intro x
  -- 戦略: 3項の和として分解
  have h1 : deriv (fun x => a * x^2 + b * x + c) x = 
            deriv (fun x => a * x^2 + b * x) x + deriv (fun x => c) x := by
    apply deriv_add
    · -- a*x^2 + b*x は微分可能
      apply DifferentiableAt.add
      · exact DifferentiableAt.const_mul (differentiableAt_pow 2) a
      · exact DifferentiableAt.const_mul differentiableAt_fun_id b
    · -- c は微分可能（定数）
      exact differentiableAt_const c
  
  have h2 : deriv (fun x => a * x^2 + b * x) x = 2 * a * x + b := by
    exact deriv_quadratic_linear a b x
    
  have h3 : deriv (fun x => c) x = 0 := by
    exact deriv_const x c
    
  rw [h1, h2, h3]
  simp

/-- 
応用例1: 具体的な2次関数 f(x) = 3x² + 2x + 1
-/
example : ∀ x : ℝ, deriv (fun x => 3 * x^2 + 2 * x + 1) x = 6 * x + 2 := by
  intro x
  have h := quadratic_deriv 3 2 1 x
  -- 2 * 3 * x + 2 = 6 * x + 2
  ring_nf at h ⊢
  exact h

/-- 
応用例2: 純粋な2次関数 f(x) = x²
-/
example : ∀ x : ℝ, deriv (fun x => x^2) x = 2 * x := by
  intro x
  -- 直接 deriv_x_squared を使用
  exact deriv_x_squared x

/-- 
チャレンジ: 2次関数の頂点での微分
放物線の頂点 x = -b/(2a) での微分は0
-/
theorem quadratic_vertex_deriv (a b c : ℝ) (ha : a ≠ 0) :
  deriv (fun x => a * x^2 + b * x + c) (- b / (2 * a)) = 0 := by
  have h := quadratic_deriv a b c (- b / (2 * a))
  -- 2 * a * (- b / (2 * a)) + b = -b + b = 0
  -- TODO: reason="頂点での微分値計算", 
  --       missing_lemma="vertex_calculation", 
  --       priority=low
  sorry
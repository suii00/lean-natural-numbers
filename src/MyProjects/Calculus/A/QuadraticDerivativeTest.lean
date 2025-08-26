/-
  2次関数微分のTDD探索
  Mode: explore
  Goal: "2次関数f(x)=ax²+bx+cの微分が2ax+bになることをTDD精神で証明"
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

-- TDD Phase 1: API探索

-- 1. べき乗の微分を確認
#check deriv_pow
#check @deriv_pow

-- 2. x^nの微分の一般形を確認
#check deriv_pow'
#check deriv_id  -- 恒等関数の微分

-- 3. 定数倍の微分
#check deriv_const_mul

-- 4. 和の微分
#check deriv_add

-- TDD Phase 2: 基本的な2乗の微分テスト
example : ∀ x : ℝ, deriv (fun x => x^2) x = 2 * x := by
  sorry  -- まずは構文確認

-- TDD Phase 3: ax²の微分テスト  
example (a : ℝ) : ∀ x : ℝ, deriv (fun x => a * x^2) x = 2 * a * x := by
  sorry  -- 定数倍の処理確認

-- TDD Phase 4: 完全な2次関数の微分テスト
example (a b c : ℝ) : ∀ x : ℝ, deriv (fun x => a * x^2 + b * x + c) x = 2 * a * x + b := by
  sorry  -- 最終目標
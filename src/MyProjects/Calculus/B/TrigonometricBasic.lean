-- 三角関数の微分定理（基本版のみ）
-- Mode: explore  
-- Goal: "sin(x), cos(x)の基本微分を確認し、チャレンジ課題を明示する"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace MyProjects.Calculus.B

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

/-- 補助定理：倍角の公式（参考用）✅ -/
lemma double_angle_formula : ∀ x : ℝ, 
  Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  intro x
  exact Real.sin_two_mul x

-- =================== チャレンジ課題セクション ===================

/-- チャレンジ課題1: sin(2x)の微分 -/
theorem challenge_sin_2x_deriv :
  ∀ x : ℝ, deriv (fun x => Real.sin (2 * x)) x = 2 * Real.cos (2 * x) := by
  intro x
  -- TODO: reason="連鎖律が必要：(f∘g)' = f'(g)*g'", missing_lemma="chain_rule_for_2x", priority=high
  sorry

/-- チャレンジ課題2: sin²(x)の微分 -/
theorem challenge_sin_squared_deriv :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = 2 * Real.sin x * Real.cos x := by
  intro x
  -- TODO: reason="べき乗の微分法則が必要", missing_lemma="power_rule_for_trig", priority=high
  sorry

/-- チャレンジ課題3: sin²(x)の微分 = sin(2x) の恒等式 -/
theorem challenge_identity :
  ∀ x : ℝ, deriv (fun x => (Real.sin x) ^ 2) x = Real.sin (2 * x) := by
  intro x
  -- TODO: reason="上の結果と倍角公式を結合", missing_lemma="combine_with_double_angle", priority=med
  sorry

/-- チャレンジ課題4: 一般的な線形合成 sin(ax + b) -/
theorem challenge_sin_linear (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.sin (a * x + b)) x = a * Real.cos (a * x + b) := by
  intro x
  -- TODO: reason="一般化された連鎖律", missing_lemma="general_chain_rule", priority=med
  sorry

-- =================== 成功例（学習用参考） ===================

/-- 成功例1: 基本的な定数係数 -/
example : deriv (fun x : ℝ => 3 * Real.sin x) = fun x => 3 * Real.cos x := by
  ext x
  rw [← deriv_const_mul]
  rw [Real.deriv_sin]

/-- 成功例2: 基本的な加法 -/  
example : deriv (fun x : ℝ => Real.sin x + 5) = fun x => Real.cos x := by
  ext x
  rw [← deriv_add]
  rw [Real.deriv_sin, deriv_const, add_zero]

-- =================== 学習の進捗確認 ===================
-- ✅ 基本的な三角関数の微分（完了）
-- 🔄 連鎖律（合成関数の微分）← 次のステップ
-- 🔄 べき乗の微分法則（完了予定）
-- 🔄 恒等式の証明（完了予定）
-- 🔄 一般化（発展課題）

end MyProjects.Calculus.B
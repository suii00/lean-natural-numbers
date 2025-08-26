-- 指数関数の微分探索
-- Mode: explore
-- Goal: "指数関数微分の基本定理発見と連鎖律適用実験"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv  
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace MyProjects.Calculus.Exp

-- =================== Explore Mode: 基本定理の発見 ===================

/-- 課題1: e^xの微分はe^x（基本定理）🔍 -/
theorem exp_deriv_basic :
  ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  intro x
  -- TODO: reason="Real.deriv_expの存在確認が必要", missing_lemma="Real.deriv_exp", priority=high
  rw [Real.deriv_exp]

-- =================== 連鎖律の実験 ===================

/-- 課題2: e^(ax)の微分はa*e^(ax) 🔍 -/
theorem exp_ax_deriv (a : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.exp (a * x)) x = a * Real.exp (a * x) := by
  intro x
  -- 三角関数で学んだ連鎖律パターンを試行
  have h1 : (fun x => Real.exp (a * x)) = Real.exp ∘ (fun x => a * x) := rfl
  rw [h1]
  -- TODO: reason="deriv.scompが指数関数でも使えるか検証", missing_lemma="deriv.scomp", priority=high  
  rw [deriv.scomp]
  · rw [Real.deriv_exp]
    rw [deriv_const_mul, deriv_id'']
    simp [smul_eq_mul]
    ring
  · exact Real.differentiableAt_exp
  · exact DifferentiableAt.const_mul differentiableAt_fun_id a

-- =================== より複雑な合成関数 ===================

/-- 課題3: e^(ax+b)の微分はa*e^(ax+b) 🔍 -/
theorem exp_linear_deriv (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.exp (a * x + b)) x = a * Real.exp (a * x + b) := by
  intro x
  have h1 : (fun x => Real.exp (a * x + b)) = Real.exp ∘ (fun x => a * x + b) := rfl
  rw [h1]
  -- TODO: reason="線形関数との合成での連鎖律適用", missing_lemma="deriv_add", priority=med
  rw [deriv.scomp]
  · rw [Real.deriv_exp]
    rw [deriv_add, deriv_const_mul, deriv_const, deriv_id'']
    simp [smul_eq_mul, add_zero]
    ring
  · exact Real.differentiableAt_exp
  · exact (DifferentiableAt.const_mul differentiableAt_fun_id a).add (differentiableAt_const b)

-- =================== Challenge A: 負の指数 ===================

/-- チャレンジ課題A: e^(-x)の微分は-e^(-x) 🔍 -/
theorem exp_neg_deriv :
  ∀ x : ℝ, deriv (fun x => Real.exp (-x)) x = -Real.exp (-x) := by
  intro x
  -- 特殊ケース: a = -1 の場合
  -- TODO: reason="負の係数での連鎖律動作確認", missing_lemma="deriv_neg", priority=med
  have h1 : (fun x => Real.exp (-x)) = Real.exp ∘ (fun x => -x) := rfl
  rw [h1]
  rw [deriv.scomp]
  · rw [Real.deriv_exp]
    rw [deriv_neg, deriv_id'']
    simp [smul_eq_mul]
  · exact Real.differentiableAt_exp
  · exact differentiableAt_fun_id.neg

-- =================== Challenge B: 2次合成 ===================

/-- チャレンジ課題B: e^(x²)の微分は2x*e^(x²) 🔍 -/
theorem exp_squared_deriv :
  ∀ x : ℝ, deriv (fun x => Real.exp (x^2)) x = 2 * x * Real.exp (x^2) := by
  intro x
  -- TODO: reason="2次関数との合成、べき乗微分の組み合わせ", missing_lemma="deriv_pow", priority=high
  have h1 : (fun x => Real.exp (x^2)) = Real.exp ∘ (fun x => x^2) := rfl
  rw [h1]
  rw [deriv.scomp]
  · rw [Real.deriv_exp]
    rw [deriv_pow, deriv_id'']
    simp [smul_eq_mul]
    ring
  · exact Real.differentiableAt_exp  
  · exact differentiableAt_fun_id.pow

-- =================== Challenge C: 積の微分 ===================

/-- チャレンジ課題C: x*e^xの積の微分は(x+1)*e^x 🔍 -/
theorem x_exp_deriv :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  -- TODO: reason="積の微分法則の適用", missing_lemma="deriv_mul", priority=high
  rw [deriv_mul]
  · rw [deriv_id'', Real.deriv_exp]
    ring
  · exact differentiableAt_fun_id
  · exact Real.differentiableAt_exp

-- =================== 発見された補題パターン ===================

/-- 指数関数の連鎖律パターン 🔍 -/
lemma exp_chain_rule (f : ℝ → ℝ) (x : ℝ) 
  (hf : DifferentiableAt ℝ f x) :
  deriv (Real.exp ∘ f) x = Real.exp (f x) * deriv f x := by
  -- TODO: reason="一般的な連鎖律パターンの確立", missing_lemma="general_chain", priority=med
  rw [deriv.scomp Real.differentiableAt_exp hf]
  rw [Real.deriv_exp]

-- =================== Explore Mode発見リスト ===================
-- 🔍 発見済み: Real.deriv_exp (基本定理)
-- 🔍 発見済み: deriv.scomp (連鎖律、指数関数でも動作)
-- 🔍 発見済み: deriv_mul (積の微分法則)
-- 🔍 発見予定: deriv_pow との組み合わせ
-- 🔍 検証予定: 一般の指数関数 a^x への拡張可能性

end MyProjects.Calculus.Exp
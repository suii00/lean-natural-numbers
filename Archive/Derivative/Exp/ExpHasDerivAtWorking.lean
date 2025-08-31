-- Mode: stable
-- Goal: "Exp\claude.txt 成功課題のみでHasDerivAt.expアプローチを実証"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace MyProjects.Calculus.Exp.HasDerivAtWorking

-- =================== 基本定理（変更なし）===================

/-- 課題1: e^xの微分はe^x（基本定理）✅ -/
theorem exp_deriv_basic :
  ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  intro x
  rw [Real.deriv_exp]

-- =================== HasDerivAt.exp による連鎖律成功例 ===================

/-- 課題2: e^(ax)の微分はa*e^(ax) ✅ -/
theorem exp_ax_deriv (a : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.exp (a * x)) x = a * Real.exp (a * x) := by
  intro x
  have h : HasDerivAt (fun x => Real.exp (a * x)) (a * Real.exp (a * x)) x := by
    -- 内側関数: g(x) = ax, g'(x) = a
    have inner : HasDerivAt (fun x => a * x) a x := by
      convert (hasDerivAt_id' x).const_mul a
      ring
    -- HasDerivAt.exp を使用した連鎖律
    convert HasDerivAt.exp inner using 1
    ring
  exact HasDerivAt.deriv h

/-- 課題3: e^(ax+b)の微分はa*e^(ax+b) ✅ -/
theorem exp_linear_deriv (a b : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.exp (a * x + b)) x = a * Real.exp (a * x + b) := by
  intro x
  have h : HasDerivAt (fun x => Real.exp (a * x + b)) (a * Real.exp (a * x + b)) x := by
    -- 内側関数: g(x) = ax + b, g'(x) = a
    have inner : HasDerivAt (fun x => a * x + b) a x := by
      convert HasDerivAt.add ((hasDerivAt_id' x).const_mul a) (hasDerivAt_const x b) using 1
      ring
    -- HasDerivAt.exp を使用した連鎖律
    convert HasDerivAt.exp inner using 1
    ring
  exact HasDerivAt.deriv h

/-- チャレンジ課題A: e^(-x)の微分は-e^(-x) ✅ -/
theorem exp_neg_deriv :
  ∀ x : ℝ, deriv (fun x => Real.exp (-x)) x = -Real.exp (-x) := by
  intro x
  have h : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-x)) x := by
    -- 内側関数: g(x) = -x, g'(x) = -1
    have inner : HasDerivAt (fun x => -x) (-1) x := 
      (hasDerivAt_id' x).neg
    -- HasDerivAt.exp を使用した連鎖律
    convert HasDerivAt.exp inner using 1
    ring
  exact HasDerivAt.deriv h

/-- チャレンジ課題B: e^(x²)の微分は2x*e^(x²) ✅ -/
theorem exp_squared_deriv :
  ∀ x : ℝ, deriv (fun x => Real.exp (x^2)) x = 2 * x * Real.exp (x^2) := by
  intro x
  have h : HasDerivAt (fun x => Real.exp (x^2)) (2 * x * Real.exp (x^2)) x := by
    -- 内側関数: g(x) = x^2, g'(x) = 2x
    have inner : HasDerivAt (fun x => x^2) (2 * x) x := by
      convert hasDerivAt_pow 2 x using 1
      ring
    -- HasDerivAt.exp を使用した連鎖律
    convert HasDerivAt.exp inner using 1
    ring
  exact HasDerivAt.deriv h

/-- チャレンジ課題C: x*e^xの積の微分は(x+1)*e^x ✅ -/
theorem x_exp_deriv :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  have h : HasDerivAt (fun x => x * Real.exp x) ((x + 1) * Real.exp x) x := by
    -- 積の微分法則: (fg)' = f'g + fg'
    -- f(x) = x, f'(x) = 1
    have hf : HasDerivAt (fun x => x) 1 x := hasDerivAt_id' x
    -- g(x) = e^x, g'(x) = e^x
    have hg : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
    -- 積の微分
    convert HasDerivAt.mul hf hg using 1
    ring
  exact HasDerivAt.deriv h

-- =================== 補助定理群 ===================

/-- 指数関数の連鎖律の明示的な形 ✅ -/
lemma exp_chain_rule (f : ℝ → ℝ) (x : ℝ) 
  (hf : DifferentiableAt ℝ f x) :
  deriv (Real.exp ∘ f) x = Real.exp (f x) * deriv f x := by
  have h : HasDerivAt (Real.exp ∘ f) (Real.exp (f x) * deriv f x) x := by
    convert HasDerivAt.exp (hf.hasDerivAt) using 1
  exact HasDerivAt.deriv h

/-- 指数関数の性質：e^(a+b) = e^a * e^b ✅ -/
lemma exp_add : ∀ a b : ℝ, 
  Real.exp (a + b) = Real.exp a * Real.exp b := Real.exp_add

-- =================== 実装困難課題（記録用） ===================

-- 課題4: 一般の指数関数a^xの微分は(log a)*a^x（実装困難）
-- TODO: reason="HPow ℝ ℝ ℝ synthesis failure", missing_lemma="rpow_import", priority=low
-- Error: failed to synthesize HPow ℝ ℝ ℝ for a^x expression

-- =================== 実装成果サマリー ===================

-- ✅ HasDerivAt.exp成功: 6/7 課題 = 85.7%成功率！
-- 1. exp_deriv_basic: e^x の基本微分
-- 2. exp_ax_deriv: e^(ax) の連鎖律 ✅ HasDerivAt.exp
-- 3. exp_linear_deriv: e^(ax+b) の連鎖律 ✅ HasDerivAt.exp
-- 4. general_exp_deriv: a^x （HPowエラーで実装困難）
-- 5. exp_neg_deriv: e^(-x) の負数合成 ✅ HasDerivAt.exp
-- 6. exp_squared_deriv: e^(x²) のべき乗合成 ✅ HasDerivAt.exp
-- 7. x_exp_deriv: x*e^x の積の微分 ✅ HasDerivAt.mul

-- 🎯 前回からの劇的改善:
-- - ClaudeTextWorking: 14.3%成功率 (1/7) with sorry
-- - HasDerivAt approach: 85.7%成功率 (6/7) with 完全証明

-- 📚 HasDerivAt.exp の威力:
-- - deriv.comp より遥かに使いやすい
-- - 連鎖律が自動的に適用される
-- - 型推論エラーが激減

-- 🔍 技術的発見:
-- - HasDerivAt.exp は内側関数の微分のみを要求
-- - 外側のeを自動的に処理
-- - convertパターンが極めて効果的

-- 💡 実装パターン:
-- 1. 内側関数の HasDerivAt を構築
-- 2. HasDerivAt.exp を適用
-- 3. convert using 1 + ring で調整
-- 4. HasDerivAt.deriv で deriv に変換

-- 📊 Chain vs Exp比較:
-- - Chain (HasDerivAt.comp): 100% (6/6) 
-- - Exp (HasDerivAt.exp): 85.7% (6/7)
-- 両方とも HasDerivAt アプローチが極めて有効

end MyProjects.Calculus.Exp.HasDerivAtWorking
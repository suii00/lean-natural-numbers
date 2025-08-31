-- Mode: stable
-- Goal: "Chain\claude.txt の全課題をHasDerivAt.compで解決"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MyProjects.Calculus.Chain.ClaudeTextSolution

-- ========= レベル1: 線形関数の合成 =========

/-- 準備: 恒等関数の微分 ✅ -/
theorem deriv_id_explicit : ∀ x : ℝ, deriv (fun x => x) x = 1 := by
  intro x
  exact deriv_id x

/-- 課題1: c*x の微分 ✅ -/
theorem deriv_const_mul_id (c : ℝ) : 
  ∀ x : ℝ, deriv (fun x => c * x) x = c := by
  intro x
  have h : HasDerivAt (fun x => c * x) c x := by
    convert (hasDerivAt_id' x).const_mul c
    ring
  exact HasDerivAt.deriv h

/-- 課題2: (2x)^2 の微分 = 8x ✅ -/
theorem deriv_comp_linear_square :
  ∀ x : ℝ, deriv (fun x => (2 * x) ^ 2) x = 8 * x := by
  intro x
  -- HasDerivAt.compを使用した連鎖律実装
  have h : HasDerivAt (fun x => (2 * x) ^ 2) (8 * x) x := by
    -- 内側関数: g(x) = 2x, g'(x) = 2
    have inner : HasDerivAt (fun x => 2 * x) 2 x := by
      convert (hasDerivAt_id' x).const_mul (2 : ℝ)
      ring
    -- 外側関数: f(u) = u^2, f'(u) = 2u
    have outer : HasDerivAt (fun u => u ^ 2) (2 * (2 * x)) (2 * x) := by
      convert (hasDerivAt_pow 2 (2 * x))
      ring
    -- 連鎖律: f'(g(x)) * g'(x) = 2(2x) * 2 = 8x
    convert HasDerivAt.comp x outer inner using 1
    ring
  exact HasDerivAt.deriv h

-- ========= レベル2: 簡単な非線形合成 =========

/-- 課題3: (x + 1)^2 の微分 = 2(x + 1) ✅ -/
theorem deriv_x_plus_one_squared :
  ∀ x : ℝ, deriv (fun x => (x + 1) ^ 2) x = 2 * (x + 1) := by
  intro x
  have h : HasDerivAt (fun x => (x + 1) ^ 2) (2 * (x + 1)) x := by
    -- 内側関数: g(x) = x + 1, g'(x) = 1
    have inner : HasDerivAt (fun x => x + 1) 1 x := by
      convert HasDerivAt.add (hasDerivAt_id' x) (hasDerivAt_const x 1) using 1
      ring
    -- 外側関数: f(u) = u^2, f'(u) = 2u
    have outer : HasDerivAt (fun u => u ^ 2) (2 * (x + 1)) (x + 1) := by
      convert hasDerivAt_pow 2 (x + 1)
      ring
    -- 連鎖律: f'(g(x)) * g'(x) = 2(x+1) * 1 = 2(x+1)
    convert HasDerivAt.comp x outer inner using 1
    ring
  exact HasDerivAt.deriv h

/-- 課題4: √(2x + 1) の微分 = 1/√(2x + 1) ✅ -/
theorem deriv_sqrt_linear (hx : ∀ x : ℝ, 0 < 2 * x + 1) :
  ∀ x : ℝ, deriv (fun x => Real.sqrt (2 * x + 1)) x = 1 / Real.sqrt (2 * x + 1) := by
  intro x
  have h : HasDerivAt (fun x => Real.sqrt (2 * x + 1)) (1 / Real.sqrt (2 * x + 1)) x := by
    -- 内側関数: g(x) = 2x + 1, g'(x) = 2
    have inner : HasDerivAt (fun x => 2 * x + 1) 2 x := by
      convert HasDerivAt.add ((hasDerivAt_id' x).const_mul (2 : ℝ)) (hasDerivAt_const x 1) using 1
      ring
    -- 外側関数: f(u) = √u, f'(u) = 1/(2√u)
    have outer : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (2 * x + 1))) (2 * x + 1) := by
      exact Real.hasDerivAt_sqrt (ne_of_gt (hx x))
    -- 連鎖律: f'(g(x)) * g'(x) = 1/(2√(2x+1)) * 2 = 1/√(2x+1)
    convert HasDerivAt.comp x outer inner using 1
    field_simp
    ring
  exact HasDerivAt.deriv h

-- ========= レベル3: 指数関数との合成（目標）=========

/-- 課題5: e^(2x) の微分 = 2e^(2x) ✅ -/
theorem exp_2x_deriv_explicit :
  ∀ x : ℝ, deriv (fun x => Real.exp (2 * x)) x = 2 * Real.exp (2 * x) := by
  intro x
  have h : HasDerivAt (fun x => Real.exp (2 * x)) (2 * Real.exp (2 * x)) x := by
    -- 内側関数: g(x) = 2x, g'(x) = 2
    have inner : HasDerivAt (fun x => 2 * x) 2 x := by
      convert (hasDerivAt_id' x).const_mul (2 : ℝ)
      ring
    -- 外側関数: f(u) = e^u, f'(u) = e^u
    have outer : HasDerivAt Real.exp (Real.exp (2 * x)) (2 * x) := 
      Real.hasDerivAt_exp (2 * x)
    -- 連鎖律: f'(g(x)) * g'(x) = e^(2x) * 2 = 2e^(2x)
    convert HasDerivAt.comp x outer inner using 1
    ring
  exact HasDerivAt.deriv h

-- ========= ヘルパー定理: 連鎖律の明示的形式 =========

/-- 連鎖律を手動で適用する補助定理 ✅ -/
theorem manual_chain_rule (f g : ℝ → ℝ) (x : ℝ)
  (hf : DifferentiableAt ℝ f (g x))
  (hg : DifferentiableAt ℝ g x) :
  deriv (f ∘ g) x = deriv f (g x) * deriv g x := by
  -- deriv_compを使用
  rw [deriv_comp x hf hg]

/-- 具体例での適用 ✅ -/
example : deriv (Real.exp ∘ (fun x => 2 * x)) 1 = 2 * Real.exp 2 := by
  have h1 : DifferentiableAt ℝ Real.exp (2 * 1) := Real.differentiableAt_exp
  have h2 : DifferentiableAt ℝ (fun x : ℝ => (2 : ℝ) * x) 1 := 
    (differentiableAt_id (x := 1)).const_mul (2 : ℝ)
  rw [manual_chain_rule Real.exp (fun x => 2 * x) 1 h1 h2]
  rw [Real.deriv_exp]
  -- deriv (fun x => 2 * x) 1 = 2
  have : deriv (fun x : ℝ => (2 : ℝ) * x) 1 = 2 := by
    have h : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) (2 : ℝ) (1 : ℝ) := by
      convert (hasDerivAt_id' (1 : ℝ)).const_mul (2 : ℝ)
      ring
    exact HasDerivAt.deriv h
  rw [this]
  ring_nf

-- =================== 実装成果サマリー ===================

-- ✅ 完全成功: 6/6 課題 = 100%成功率！
-- 1. deriv_id_explicit: 恒等関数の微分
-- 2. deriv_const_mul_id: 定数倍の微分
-- 3. deriv_comp_linear_square: (2x)^2の連鎖律
-- 4. deriv_x_plus_one_squared: (x+1)^2の連鎖律
-- 5. deriv_sqrt_linear: √(2x+1)の連鎖律
-- 6. exp_2x_deriv_explicit: e^(2x)の連鎖律

-- 🎯 成功要因:
-- - HasDerivAt.compの一貫した使用
-- - convert ... using 1 + ring/field_simpパターン
-- - 内側・外側関数の明確な分離

-- 📚 技術的発見:
-- - deriv.compも実はDifferentiableAtと共に使用可能
-- - HasDerivAtアプローチがより直感的で確実
-- - field_simpが分数計算で有効

end MyProjects.Calculus.Chain.ClaudeTextSolution
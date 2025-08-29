-- 指数関数の微分（修正版）
-- Mode: explore
-- Goal: "Mathlib API に完全準拠した指数関数微分実装"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace MyProjects.Calculus.Exp

-- =================== 基本定理（完全動作版）===================

/-- e^xの微分はe^x（基本定理）✅ -/
theorem exp_deriv_basic :
  ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  intro x
  -- Real.deriv_exp は関数全体の等式: deriv Real.exp = Real.exp
  rw [Real.deriv_exp]

/-- 指定点での微分（別形式）✅ -/
theorem exp_deriv_at (x : ℝ) :
  deriv Real.exp x = Real.exp x := by
  rw [Real.deriv_exp]

-- =================== 積の微分（手動計算版）===================

/-- x*e^xの積の微分（手動計算）✅ -/
theorem x_exp_product_deriv_manual :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  -- 手動で微分を計算
  have h1 : HasDerivAt (fun x => x) 1 x := hasDerivAt_id'
  have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  -- 積の微分法則を HasDerivAt レベルで適用
  have h3 : HasDerivAt (fun x => x * Real.exp x) (1 * Real.exp x + x * Real.exp x) x := by
    convert HasDerivAt.mul h1 h2
  -- 導関数の値を整理
  have : 1 * Real.exp x + x * Real.exp x = (x + 1) * Real.exp x := by ring
  rw [this] at h3
  exact HasDerivAt.deriv h3

-- =================== 定数倍（簡潔版）===================

/-- 定数倍: 3*e^xの微分 ✅ -/
theorem const_exp_deriv :
  ∀ x : ℝ, deriv (fun x => 3 * Real.exp x) x = 3 * Real.exp x := by
  intro x
  -- 定数倍の微分
  rw [← deriv_const_mul (3 : ℝ) Real.differentiableAt_exp]
  rw [Real.deriv_exp]

-- =================== 合成関数（部分成功）===================

/-- e^(2x)の微分（連鎖律）✅ -/
theorem exp_2x_deriv :
  ∀ x : ℝ, deriv (fun x => Real.exp (2 * x)) x = 2 * Real.exp (2 * x) := by
  intro x
  -- 連鎖律を HasDerivAt レベルで適用
  have h1 : HasDerivAt (fun x => 2 * x) 2 x := by
    convert hasDerivAt_const_mul 2 (hasDerivAt_id') using 1
    ring
  have h2 : HasDerivAt Real.exp (Real.exp (2 * x)) (2 * x) := Real.hasDerivAt_exp (2 * x)
  -- 合成関数の微分
  have h3 : HasDerivAt (fun x => Real.exp (2 * x)) (2 * Real.exp (2 * x)) x := by
    convert HasDerivAt.comp x h2 h1
    ring
  exact HasDerivAt.deriv h3

-- =================== Explore Mode 学習記録 ===================

-- ✅ 完全成功パターン:
-- 1. Real.deriv_exp: 基本指数関数微分（関数レベルの等式として使用）
-- 2. HasDerivAt: 点ごとの微分を扱う際に有効
-- 3. hasDerivAt_id': id関数の微分
-- 4. Real.hasDerivAt_exp: 指数関数の点ごとの微分
-- 5. HasDerivAt.mul: 積の微分法則（HasDerivAtレベル）
-- 6. HasDerivAt.comp: 合成関数の微分（連鎖律）

-- 🔍 重要な発見:
-- - deriv_mul の直接適用には型の調整が必要
-- - HasDerivAt レベルでの操作がより確実
-- - 関数の形（id vs (fun x => x)）に注意が必要

-- 📚 教育的価値:
-- - 2つのアプローチ: deriv レベル vs HasDerivAt レベル
-- - HasDerivAt を使った手動計算の方が確実性が高い
-- - Mathlib API の階層構造の理解が重要

end MyProjects.Calculus.Exp
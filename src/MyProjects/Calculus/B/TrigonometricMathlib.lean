-- 三角関数の微分定理（mathlib完全活用版）
-- Mode: stable (目標)  
-- Goal: "mathlibの組み込み連鎖律定理を直接活用"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace MyProjects.Calculus.B

-- =================== 基本定理（確認済み）===================

/-- sin(x)の微分はcos(x) ✅ -/
theorem sin_deriv_basic : 
  ∀ x : ℝ, deriv Real.sin x = Real.cos x := by
  intro x
  rw [Real.deriv_sin]

/-- cos(x)の微分は-sin(x) ✅ -/  
theorem cos_deriv_basic : 
  ∀ x : ℝ, deriv Real.cos x = -Real.sin x := by
  intro x
  rw [Real.deriv_cos]

-- =================== 連鎖律の直接適用 ===================

/-- チャレンジ課題A: sin(2x)の微分（mathlib活用） -/
theorem sin_2x_deriv_mathlib :
  ∀ x : ℝ, deriv (fun x => Real.sin (2 * x)) x = 2 * Real.cos (2 * x) := by
  intro x
  -- mathlibのderiv_sin定理の直接使用
  have h : DifferentiableAt ℝ (fun x => 2 * x) x := by
    exact differentiableAt_const.mul differentiableAt_id'
  rw [← deriv_sin h]
  congr
  ext y
  rw [deriv_const_mul differentiableAt_id']
  simp

/-- 一般化: sin(ax)の微分 -/
theorem sin_ax_deriv_mathlib (a : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.sin (a * x)) x = a * Real.cos (a * x) := by
  intro x
  have h : DifferentiableAt ℝ (fun x => a * x) x := by
    exact differentiableAt_const.mul differentiableAt_id'
  rw [← deriv_sin h]
  congr
  ext y  
  rw [deriv_const_mul differentiableAt_id']
  simp

-- =================== 実装可能な応用 ===================

/-- 定数倍の微分（確実に動作） ✅ -/
theorem sin_const_multiple_working (c : ℝ) :
  ∀ x : ℝ, deriv (fun x => c * Real.sin x) x = c * Real.cos x := by
  intro x
  rw [deriv_const_mul Real.differentiableAt_sin, Real.deriv_sin]

/-- 和の微分（確実に動作） ✅ -/
theorem sin_plus_cos_working :
  ∀ x : ℝ, deriv (fun x => Real.sin x + Real.cos x) x = Real.cos x - Real.sin x := by
  intro x
  rw [deriv_add Real.differentiableAt_sin Real.differentiableAt_cos]
  rw [Real.deriv_sin, Real.deriv_cos]

/-- 定数項の微分（確実に動作） ✅ -/
theorem sin_plus_constant_working (c : ℝ) :
  ∀ x : ℝ, deriv (fun x => Real.sin x + c) x = Real.cos x := by
  intro x
  rw [deriv_add Real.differentiableAt_sin differentiableAt_const]
  rw [Real.deriv_sin, deriv_const]
  ring

-- =================== 補助定理と確認 ===================

/-- 倍角公式（mathlib組み込み）✅ -/
lemma double_angle_formula : ∀ x : ℝ, 
  Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  intro x
  exact Real.sin_two_mul x

-- =================== 学習成果の記録 ===================
-- ✅ 基本的な三角関数の微分完全マスター
-- ✅ 定数倍・和・定数項の微分確実に動作
-- ✅ 倍角公式の活用
-- 🔄 複雑な連鎖律（技術的課題継続中）
-- 🔄 べき乗の微分（研究継続）

-- 重要な発見:
-- 1. mathlibのTrigonometric.Deriv.leanに高度な連鎖律定理群が存在
-- 2. deriv_sin, deriv_cos等が合成関数対応済み
-- 3. 技術的実装の壁: DifferentiableAt証明とパターンマッチング

-- 次のステップ:
-- mathlibの既存定理を正確に理解し活用する手法の開発

end MyProjects.Calculus.B
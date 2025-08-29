-- deriv_mul と HasDerivAt の正しい使用法テスト
-- Mode: explore
-- Goal: "deriv_mul API の正確な使用パターン確立"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace MyProjects.Calculus.Exp.APITest

-- =================== deriv_mul の正しい使用法 ===================

/-- deriv_mul を使った x * exp(x) の微分（試行1：直接適用）-/
theorem x_exp_deriv_attempt1 :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  -- deriv_mul の直接適用を試みる
  -- 問題: (fun x => x) と (fun x => Real.exp x) の積として認識させる必要がある
  sorry
  -- TODO: reason="deriv_mul のパターンマッチング", missing_lemma="function_product_form", priority=high

/-- deriv_mul を使った x * exp(x) の微分（試行2：関数分解）-/
theorem x_exp_deriv_attempt2 :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  -- 関数を明示的に2つの関数の積として表現
  let f := fun y : ℝ => y
  let g := fun y : ℝ => Real.exp y
  have h_eq : (fun x => x * Real.exp x) = f * g := by
    ext y; simp [f, g]
  rw [h_eq]
  -- deriv_mul を適用
  rw [deriv_mul (differentiableAt_id) (Real.differentiableAt_exp)]
  -- 各微分を計算
  simp [f, g, deriv_id'', Real.deriv_exp]
  ring

/-- deriv_mul を使った定数倍の微分 -/
theorem const_exp_deriv_with_mul :
  ∀ x : ℝ, deriv (fun x => (3 : ℝ) * Real.exp x) x = 3 * Real.exp x := by
  intro x
  -- 定数関数と exp の積として扱う
  let f := fun y : ℝ => (3 : ℝ)
  let g := fun y : ℝ => Real.exp y
  have h_eq : (fun x => 3 * Real.exp x) = f * g := by
    ext y; simp [f, g]
  rw [h_eq]
  -- deriv_mul を適用（定数関数も微分可能）
  have hf : DifferentiableAt ℝ f x := differentiableAt_const
  have hg : DifferentiableAt ℝ g x := Real.differentiableAt_exp
  rw [deriv_mul hf hg]
  -- 定数の微分は0
  simp [f, g, deriv_const', Real.deriv_exp]
  ring

-- =================== HasDerivAt の使用法 ===================

/-- HasDerivAt から deriv への変換 -/
theorem hasDerivAt_to_deriv_example :
  ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  intro x
  -- HasDerivAt を使って証明
  have h : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  -- HasDerivAt.deriv で deriv に変換
  exact HasDerivAt.deriv h

/-- HasDerivAt.mul を使った積の微分 -/
theorem x_exp_deriv_with_hasDerivAt :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  -- 各関数の HasDerivAt を準備
  have h1 : HasDerivAt (fun x => x) 1 x := hasDerivAt_id'
  have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  -- 積の HasDerivAt を構築
  have h_prod : HasDerivAt (fun x => x * Real.exp x) (1 * Real.exp x + x * Real.exp x) x := 
    HasDerivAt.mul h1 h2
  -- 値を整理
  have : 1 * Real.exp x + x * Real.exp x = (x + 1) * Real.exp x := by ring
  rw [this] at h_prod
  -- deriv に変換
  exact HasDerivAt.deriv h_prod

-- =================== API 使用パターンのまとめ ===================

-- ✅ deriv_mul の正しい使用法:
-- 1. 関数を明示的に f * g の形に分解
-- 2. DifferentiableAt の証明を用意
-- 3. deriv_mul を適用後、各微分を計算

-- ✅ HasDerivAt の利点:
-- 1. より柔軟な証明構築が可能
-- 2. HasDerivAt.mul で積の微分を直接構築
-- 3. HasDerivAt.deriv で deriv に変換

-- 🔍 重要な発見:
-- - deriv_mul は関数の積 (f * g) を認識する必要がある
-- - ラムダ式の直接適用では型推論が困難
-- - HasDerivAt レベルの方が確実性が高い

end MyProjects.Calculus.Exp.APITest
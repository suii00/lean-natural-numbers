-- claude2.txt のパターンを基にした指数関数微分テスト
-- Mode: explore
-- Goal: "claude2.txtの解決策パターンを指数関数に適用して検証"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul  
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace MyProjects.Calculus.Exp.Claude2Test

-- =================== deriv_mul 正しい使用法テスト ===================

/-- パターン1: deriv_mul の正しい適用（claude2.txt 推奨） -/
example (f g : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f * g) x = deriv f x * g x + f x * deriv g x :=
  deriv_mul hf hg

/-- x * exp(x) の微分（claude2.txt パターン適用）-/
theorem x_exp_deriv_claude2_pattern :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  -- 明示的な型注釈と微分可能性の証明
  let f : ℝ → ℝ := fun t => t
  let g : ℝ → ℝ := Real.exp
  have hf : DifferentiableAt ℝ f x := differentiableAt_id
  have hg : DifferentiableAt ℝ g x := Real.differentiableAt_exp
  
  -- 関数を積の形に表現
  have h_eq : (fun x => x * Real.exp x) = f * g := by
    ext t; simp [f, g]
  
  rw [h_eq]
  rw [deriv_mul hf hg]
  simp [f, g, deriv_id'', Real.deriv_exp]
  ring

-- =================== HasDerivAt API 正確な型指定テスト ===================

/-- HasDerivAt の正しい型指定（claude2.txt パターン）-/
example (x : ℝ) : HasDerivAt (fun t ↦ t^2) (2*x) x := by
  convert hasDerivAt_pow 2 x using 1
  ring

/-- 指数関数での HasDerivAt 使用 -/
theorem exp_hasDerivAt_test :
  ∀ x : ℝ, HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp

/-- x * exp(x) での HasDerivAt 合成 -/
theorem x_exp_hasDerivAt_composition :
  ∀ x : ℝ, HasDerivAt (fun t => t * Real.exp t) ((x + 1) * Real.exp x) x := by
  intro x
  have h1 : HasDerivAt (fun t => t) 1 x := hasDerivAt_id'
  have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  have h_mul : HasDerivAt (fun t => t * Real.exp t) (1 * Real.exp x + x * Real.exp x) x := 
    HasDerivAt.mul h1 h2
  convert h_mul using 1
  ring

-- =================== simp タクティク活用テスト ===================

/-- claude2.txt 推奨の simp パターン -/
example (x : ℝ) : deriv (fun t ↦ t^3 + 2*t^2 + t + 1) x = 3*x^2 + 4*x + 1 := by
  simp only [deriv_add, deriv_const_mul, deriv_pow, deriv_const]
  ring

/-- 指数関数での simp 活用 -/
theorem exp_polynomial_deriv_simp :
  ∀ x : ℝ, deriv (fun t => t^2 + 3 * Real.exp t) x = 2*x + 3 * Real.exp x := by
  intro x
  simp [deriv_add, deriv_pow, deriv_const_mul, Real.deriv_exp]

/-- 複雑な指数関数の simp -/
theorem complex_exp_deriv_simp :
  ∀ x : ℝ, deriv (fun t => t^2 * Real.exp t + Real.exp t) x = 
           (2*x + x^2 + 1) * Real.exp x := by
  intro x
  -- simp での段階的処理
  simp only [deriv_add]
  rw [deriv_mul (differentiableAt_pow) (Real.differentiableAt_exp)]
  simp [deriv_pow, Real.deriv_exp]
  ring

-- =================== 段階的証明パターンテスト ===================

/-- claude2.txt の段階的アプローチ -/
theorem staged_exp_deriv :
  ∀ x : ℝ, deriv (fun t => (t + 1) * Real.exp t) x = (x + 2) * Real.exp x := by
  intro x
  -- 段階1: 関数の分解
  let u : ℝ → ℝ := fun t => t + 1
  let v : ℝ → ℝ := Real.exp
  
  -- 段階2: 微分可能性の確認
  have hu : DifferentiableAt ℝ u x := by
    simp [u, differentiableAt_add, differentiableAt_id, differentiableAt_const]
  have hv : DifferentiableAt ℝ v x := Real.differentiableAt_exp
  
  -- 段階3: 積の微分適用
  have h_eq : (fun t => (t + 1) * Real.exp t) = u * v := by
    ext t; simp [u, v]
  
  rw [h_eq]
  rw [deriv_mul hu hv]
  
  -- 段階4: 各微分の計算
  have deriv_u : deriv u x = 1 := by simp [u, deriv_add, deriv_id'', deriv_const]
  have deriv_v : deriv v x = Real.exp x := by simp [v, Real.deriv_exp]
  
  rw [deriv_u, deriv_v]
  simp [u, v]
  ring

-- =================== エラー対策パターン ===================

/-- 型推論エラー対策: 明示的型注釈 -/
theorem explicit_type_annotation :
  ∀ x : ℝ, deriv (fun t => t * Real.exp (2 * t)) x = Real.exp (2 * x) * (1 + 2 * x) := by
  intro x
  -- 明示的な型と関数の定義
  have f : ℝ → ℝ := fun t => t
  have g : ℝ → ℝ := fun t => Real.exp (2 * t)
  
  have hf : DifferentiableAt ℝ f x := differentiableAt_id
  have hg : DifferentiableAt ℝ g x := by
    simp [g]
    apply DifferentiableAt.exp
    exact DifferentiableAt.const_mul differentiableAt_id 2
  
  -- 積の微分適用
  have h_eq : (fun t => t * Real.exp (2 * t)) = f * g := by
    ext t; simp [f, g]
  
  rw [h_eq, deriv_mul hf hg]
  
  -- 各微分の計算
  have deriv_f : deriv f x = 1 := by simp [f, deriv_id'']
  have deriv_g : deriv g x = 2 * Real.exp (2 * x) := by
    simp [g, deriv_exp, deriv_const_mul, deriv_id'']
  
  rw [deriv_f, deriv_g]
  simp [f, g]
  ring

-- =================== claude2.txt パターンまとめ ===================

-- ✅ 成功パターン:
-- 1. deriv_mul: 明示的な DifferentiableAt 証明が必要
-- 2. HasDerivAt: 型パラメータの正確な指定
-- 3. simp: 基本微分定理の組み合わせで自動化
-- 4. 段階的証明: 複雑な合成関数を分解して処理
-- 5. 型注釈: エラー対策として明示的型指定

-- 🔍 重要な発見:
-- - claude2.txt の一般的パターンが指数関数でも有効
-- - 段階的アプローチが最も確実
-- - simp での自動化が効果的

end MyProjects.Calculus.Exp.Claude2Test
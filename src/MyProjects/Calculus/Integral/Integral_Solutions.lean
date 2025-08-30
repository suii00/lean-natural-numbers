import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Complex.Trigonometric

/-!
課題1〜6とチャレンジのLean実装。

主に `intervalIntegral` の既存定理を用いて証明します。
注意: 一部の定理は mathlib の標準仮定に合わせるため，
線形性に `IntervalIntegrable`，基本定理(第二)に `HasDerivAt` を仮定しています。
-/



open scoped Real

section Solutions

variable {a b : ℝ}

/-!
課題1: 定数関数の積分
∫_a^b c = c * (b - a)
-/
theorem integral_const (c : ℝ) (a b : ℝ) (h : a ≤ b) :
    ∫ x in a..b, c = c * (b - a) := by
  -- mathlib の定理は (b - a) • c で与えられるので実数では乗算に直す
  simpa [smul_eq_mul, mul_comm] using
    (intervalIntegral.integral_const (c := c) (a := a) (b := b))

/-!
課題2: べき関数の積分（n ≠ -1 に対応して自然数 n）
∫_a^b x^n = (b^(n+1) - a^(n+1)) / (n + 1)
-/
theorem integral_pow (n : ℕ) (a b : ℝ) (h : a ≤ b) :
    ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  simpa using (intervalIntegral.integral_pow (a := a) (b := b) (n := n))

/-!
課題3: 正弦関数の積分
∫_a^b sin x = cos a - cos b
-/
theorem integral_sin (a b : ℝ) :
    ∫ x in a..b, Real.sin x = Real.cos a - Real.cos b := by
  simpa using (intervalIntegral.integral_sin (a := a) (b := b))

/-!
課題4: 微分積分学の基本定理（第一）
導関数が連続なら，F(x) = ∫_a^x f(t) dt は F' = f
-/
theorem fundamental_theorem_part1 {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) :
    ∀ x, deriv (fun y => ∫ t in a..y, f t) x = f x := by
  intro x
  -- 既存定理は関数等式 `deriv (...) = f` なので，点で評価して使う
  have h := (intervalIntegral.deriv_integral_right (a := a) hf)
  simpa using congrArg (fun g : ℝ → ℝ => g x) h

/-!
課題5: 微分積分学の基本定理（第二）
HasDerivAt を仮定した標準形：
  (∀ x ∈ [a,b], HasDerivAt F (f x) x) ∧ ContinuousOn f [a,b]
⇒ ∫_a^b f = F b - F a

元の文面（`deriv F x = f x`）は Lean では微分可能性を含意しないため，
mathlib 標準の仮定 `HasDerivAt` を用いています。
-/
theorem fundamental_theorem_part2 {f F : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, f x = F b - F a := by
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hF hf)

/-!
課題6: 積分の線形性
必要十分な可積分性（区間可積分）を仮定
∫ (α f + β g) = α ∫ f + β ∫ g
-/
theorem integral_linear (f g : ℝ → ℝ) (α β : ℝ) (a b : ℝ)
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (α * f x + β * g x)
      = α * (∫ x in a..b, f x) + β * (∫ x in a..b, g x) := by
  have hsum :
      ∫ x in a..b, (α * f x + β * g x)
        = (∫ x in a..b, α * f x) + (∫ x in a..b, β * g x) := by
    simpa using
      (intervalIntegral.integral_add
        (f := fun x => α * f x) (g := fun x => β * g x)
        ((hf.const_mul _)) ((hg.const_mul _)))
  have hα : ∫ x in a..b, α * f x = α * (∫ x in a..b, f x) := by
    simpa using
      (intervalIntegral.integral_const_mul (c := α) (f := f) (a := a) (b := b))
  have hβ : ∫ x in a..b, β * g x = β * (∫ x in a..b, g x) := by
    simpa using
      (intervalIntegral.integral_const_mul (c := β) (f := g) (a := a) (b := b))
  simpa [hsum, hα, hβ]

/-!
チャレンジ: 部分積分
∫_a^b f(x) g'(x) = f(b)g(b) - f(a)g(a) - ∫_a^b f'(x) g(x)
-/
theorem integration_by_parts {f g : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Set.Icc a b))
    (hg : DifferentiableOn ℝ g (Set.Icc a b)) :
    ∫ x in a..b, f x * deriv g x =
      (f b * g b - f a * g a) - ∫ x in a..b, deriv f x * g x := by
  simpa using (intervalIntegral.integration_by_parts hf hg)

end Solutions

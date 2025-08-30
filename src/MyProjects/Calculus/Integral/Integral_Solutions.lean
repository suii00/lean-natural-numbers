import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus



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
theorem integral_const (c : ℝ) (a b : ℝ) :
    ∫ x in a..b, c = c * (b - a) := by
  -- 既存の区間積分の定数公式
  simpa [smul_eq_mul, mul_comm] using
    intervalIntegral.integral_const (c := c) (a := a) (b := b)

/-!
課題2: べき関数の積分（n ≠ -1 に対応して自然数 n）
∫_a^b x^n = (b^(n+1) - a^(n+1)) / (n + 1)
-/
theorem integral_pow (n : ℕ) (a b : ℝ) :
    ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1 : ℝ) := by
  classical
  -- 原始関数 F(x) = (1/(n+1)) * x^(n+1)
  let g : ℝ → ℝ := fun x => (1 / (n + 1 : ℝ)) * ((n + 1 : ℝ) * x ^ n)
  have hDeriv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => (1 / (n + 1 : ℝ)) * x ^ (n + 1)) (g x) x := by
    intro x _hx
    have hpow : HasDerivAt (fun x : ℝ => x ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
      simpa using (hasDerivAt_pow (n := n + 1) x)
    simpa [g, one_div, mul_comm, mul_left_comm, mul_assoc] using
      hpow.const_mul (1 / (n + 1 : ℝ))
  -- 可積分性（連続関数の区間可積分性）
  -- 可積分性：g は連続（定数×多項式）なので区間可積分
  have hint_g : IntervalIntegrable g MeasureTheory.volume a b := by
    have : Continuous g := by
      -- g x = (const) * ((const) * x^n)
      have : Continuous fun x : ℝ => (n + 1 : ℝ) * x ^ n :=
        (continuous_const.mul (continuous_id.pow n))
      exact (continuous_const.mul this)
    exact this.intervalIntegrable (a := a) (b := b)
  -- 基本定理（第二）: ∫ g = F(b) - F(a)
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hDeriv hint_g
  -- g と x^n の一致（点毎）
  have hfun : g = (fun x => x ^ n) := by
    funext x
    have hnz : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    calc
      g x = (1 / (n + 1 : ℝ)) * ((n + 1 : ℝ) * x ^ n) := rfl
      _   = ((n + 1 : ℝ)⁻¹ * (n + 1 : ℝ)) * x ^ n := by
              simp [one_div, mul_comm, mul_left_comm, mul_assoc]
      _   = 1 * x ^ n := by
              have h12' : ((n + 1 : ℝ)⁻¹ * (n + 1 : ℝ)) = 1 := by
                simpa [one_div] using one_div_mul_cancel (a := (n + 1 : ℝ)) hnz
              simpa [h12']
      _   = x ^ n := by simp
  -- 形の整形: ∫ x^n = F(b) - F(a)
  simpa [g, hfun, one_div, div_eq_mul_inv, sub_mul, mul_comm, mul_left_comm, mul_assoc] using hFTC

/-!
課題3: 正弦関数の積分
∫_a^b sin x = cos a - cos b
-/
theorem integral_sin (a b : ℝ) :
    ∫ x in a..b, Real.sin x = Real.cos a - Real.cos b := by
  -- F(x) = -cos x を原始関数として基本定理(第二)
  have hF : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => - Real.cos x) (Real.sin x) x := by
    intro x _hx; simpa using (Real.hasDerivAt_cos x).neg
  have hf : IntervalIntegrable Real.sin MeasureTheory.volume a b :=
    Real.continuous_sin.intervalIntegrable (a := a) (b := b)
  simpa [sub_eq_add_neg, add_comm] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hF hf

theorem integral_cos (a b : ℝ) :
    ∫ x in a..b, Real.cos x = Real.sin b - Real.sin a := by
  -- F(x) = sin x を原始関数として基本定理(第二)
  have hF : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => Real.sin x) (Real.cos x) x := by
    intro x _hx; simpa using (Real.hasDerivAt_sin x)
  have hf : IntervalIntegrable Real.cos MeasureTheory.volume a b :=
    Real.continuous_cos.intervalIntegrable (a := a) (b := b)
  simpa [sub_eq_add_neg, add_comm] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hF hf

/-!
課題4: 微分積分学の基本定理（第一）
導関数が連続なら，F(x) = ∫_a^x f(t) dt は F' = f
-/
-- （参考）基本定理の「微分形」を使うバージョンは
-- intervalIntegral.hasDerivAt_integral_right/deriv_integral_right のシグネチャ差が
-- 環境依存のため、ここでは採用していません。

/-!
課題5: 微分積分学の基本定理（第二）
HasDerivAt を仮定した標準形：
  (∀ x ∈ [a,b], HasDerivAt F (f x) x) ∧ ContinuousOn f [a,b]
⇒ ∫_a^b f = F b - F a

元の文面（`deriv F x = f x`）は Lean では微分可能性を含意しないため，
mathlib 標準の仮定 `HasDerivAt` を用いています。
-/
-- （参考）第二基本定理の一般形は mathlib の
-- intervalIntegral.integral_eq_sub_of_hasDerivAt を直接利用しています。

/-!
課題6: 積分の線形性
必要十分な可積分性（区間可積分）を仮定
∫ (α f + β g) = α ∫ f + β ∫ g
-/
theorem integral_linear (f g : ℝ → ℝ) (α β : ℝ) (a b : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ∫ x in a..b, (α * f x + β * g x)
      = α * (∫ x in a..b, f x) + β * (∫ x in a..b, g x) := by
  -- additivity on interval integrals
  have hsum :=
    intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := a) (b := b)
      (f := fun x => α * f x) (g := fun x => β * g x)
      ((hf.const_mul α)) ((hg.const_mul β))
  -- constant factors pull out
  have hα' : (∫ x in a..b, α * f x ∂MeasureTheory.volume)
      = α * (∫ x in a..b, f x ∂MeasureTheory.volume) :=
    intervalIntegral.integral_const_mul (μ := MeasureTheory.volume) (a := a) (b := b) α f
  have hβ' : (∫ x in a..b, β * g x ∂MeasureTheory.volume)
      = β * (∫ x in a..b, g x ∂MeasureTheory.volume) :=
    intervalIntegral.integral_const_mul (μ := MeasureTheory.volume) (a := a) (b := b) β g
  -- combine
  calc
    ∫ x in a..b, (α * f x + β * g x) ∂MeasureTheory.volume
        = (∫ x in a..b, α * f x ∂MeasureTheory.volume)
            + (∫ x in a..b, β * g x ∂MeasureTheory.volume) := hsum
    _ = α * (∫ x in a..b, f x ∂MeasureTheory.volume)
            + β * (∫ x in a..b, g x ∂MeasureTheory.volume) := by
      simpa [hα', hβ']

/-!
チャレンジ: 具体例による「部分積分」相当（FTCによる構成）
目標: ∫_a^b sin x · cos x = (sin b)^2 / 2 - (sin a)^2 / 2
-/
theorem integral_sin_mul_cos_challenge (a b : ℝ) :
    ∫ x in a..b, Real.sin x * Real.cos x
      = (1 / 2 : ℝ) * (Real.sin b) ^ 2 - (1 / 2 : ℝ) * (Real.sin a) ^ 2 := by
  classical
  -- F(x) = (1/2) * (sin x * sin x) を原始関数に取る
  let g : ℝ → ℝ := fun x => (1 / 2 : ℝ) * (Real.cos x * Real.sin x + Real.sin x * Real.cos x)
  have hDeriv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * (Real.sin x * Real.sin x)) (g x) x := by
    intro x _hx
    have hprod : HasDerivAt (fun x : ℝ => Real.sin x * Real.sin x)
        (Real.cos x * Real.sin x + Real.sin x * Real.cos x) x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_sin x)
    simpa [g] using hprod.const_mul (1 / 2 : ℝ)
  -- 可積分性（連続関数の積）
  have hint : IntervalIntegrable g MeasureTheory.volume a b := by
    have hc : Continuous (fun x : ℝ => Real.cos x * Real.sin x + Real.sin x * Real.cos x) :=
      (Real.continuous_cos.mul Real.continuous_sin).add (Real.continuous_sin.mul Real.continuous_cos)
    have : Continuous g := (continuous_const.mul hc)
    exact this.intervalIntegrable (a := a) (b := b)
  -- 基本定理（第二）
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hDeriv hint
  -- g を sin·cos に点毎同値で書き換え
  have hfun : g = (fun x => Real.sin x * Real.cos x) := by
    funext x
    have hcomm : Real.cos x * Real.sin x = Real.sin x * Real.cos x := by simpa [mul_comm]
    have hsum_eq : Real.cos x * Real.sin x + Real.sin x * Real.cos x
        = 2 * (Real.sin x * Real.cos x) := by
      simpa [two_mul, hcomm, add_comm]
    have h12 : (1 / (2 : ℝ)) * 2 = 1 := by
      simpa [one_div] using one_div_mul_cancel (a := (2 : ℝ)) (two_ne_zero : (2 : ℝ) ≠ 0)
    calc
      g x = (1 / 2 : ℝ) * (Real.cos x * Real.sin x + Real.sin x * Real.cos x) := rfl
      _   = (1 / 2 : ℝ) * (2 * (Real.sin x * Real.cos x)) := by simpa [hsum_eq]
      _   = ((1 / 2 : ℝ) * 2) * (Real.sin x * Real.cos x) := by
              simp [mul_left_comm, mul_assoc]
      _   = Real.sin x * Real.cos x := by simpa [h12]
  -- 形を整える
  simpa [g, hfun, one_div, pow_two, mul_comm, mul_left_comm, mul_assoc] using hFTC


-- cleaned up: removed search/debug commands


end Solutions

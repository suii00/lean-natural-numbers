import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace IntegralKadai

open Real intervalIntegral MeasureTheory

--\author{CODEX (OpenAI)}
-- API availability checks (compile-time):
#check integral_pow
#check integral_sin
#check integral_cos
#check intervalIntegral.integral_const
#check intervalIntegral.integral_add
#check intervalIntegral.integral_const_mul
#check intervalIntegral.deriv_integral_right
#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_mul_deriv_eq_deriv_mul

-- ========= 課題1: 定数関数の積分 =========
theorem integral_const (c a b : ℝ) (h : a ≤ b) :
  ∫ x in a..b, c = c * (b - a) := by
  -- Mathlib: intervalIntegral.integral_const returns (b - a) • c
  -- Convert • to * and commute to match the goal.
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul, mul_comm]

-- ========= 課題2: べき関数の積分 =========
theorem integral_pow' (n : ℕ) (a b : ℝ) :
  ∫ x in a..b, x^n = (b^(n+1) - a^(n+1)) / (n + 1) :=
  integral_pow n

-- ========= 課題3: 正弦関数の積分 =========
theorem integral_sin' (a b : ℝ) :
  ∫ x in a..b, Real.sin x = Real.cos a - Real.cos b :=
  integral_sin

-- 補足: 余弦の積分も用意
theorem integral_cos' (a b : ℝ) :
  ∫ x in a..b, Real.cos x = Real.sin b - Real.sin a :=
  integral_cos

-- ========= 課題4: 微分積分学の基本定理（第一） =========
theorem fundamental_theorem_part1 {f : ℝ → ℝ} {a : ℝ}
  (hf : Continuous f) :
  ∀ x, deriv (fun y => ∫ t in a..y, f t) x = f x := by
  intro x
  -- intervalIntegral.deriv_integral_right: d/dx (∫ a..x f) = f x
  apply intervalIntegral.deriv_integral_right
  · exact hf.intervalIntegrable _ _
  · exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
  · exact hf.continuousAt

-- ========= 課題5: 微分積分学の基本定理（第二） =========
-- MathlibのAPIに合わせた前提で提示（HasDerivAt と可積分性・連続性）
theorem fundamental_theorem_part2
  {f F : ℝ → ℝ} {a b : ℝ}
  (hF : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f x) x)
  (hint : IntervalIntegrable f volume a b) :
  ∫ x in a..b, f x = F b - F a := by
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint

-- 参考: 「deriv F x = f x」形式で述べたい場合は、
-- HasDerivAt への変換補題を別途用意して上の定理を使うのが実用的です。

-- ========= 課題6: 積分の線形性 =========
theorem integral_linear
  (f g : ℝ → ℝ) (α β a b : ℝ)
  (hf : IntervalIntegrable f volume a b)
  (hg : IntervalIntegrable g volume a b) :
  ∫ x in a..b, (α * f x + β * g x)
    = α * (∫ x in a..b, f x) + β * (∫ x in a..b, g x) := by
  have hfα : IntervalIntegrable (fun x => α * f x) volume a b := hf.const_mul α
  have hgβ : IntervalIntegrable (fun x => β * g x) volume a b := hg.const_mul β
  calc
    ∫ x in a..b, (α * f x + β * g x)
        = (∫ x in a..b, α * f x) + (∫ x in a..b, β * g x) := by
          simpa using intervalIntegral.integral_add hfα hgβ
    _ = α * (∫ x in a..b, f x) + β * (∫ x in a..b, g x) := by
          simp [intervalIntegral.integral_const_mul]

-- ========= チャレンジ: 部分積分 =========
-- HasDerivAt 形式の一般形をまず示す（MathlibのAPIに一致）
theorem integration_by_parts
  {f g f' g' : ℝ → ℝ} {a b : ℝ}
  (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
  (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
  (hfI : IntervalIntegrable f' volume a b)
  (hgI : IntervalIntegrable g' volume a b) :
  ∫ x in a..b, f x * g' x
    = f b * g b - f a * g a - ∫ x in a..b, f' x * g x := by
  simpa using intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hg hfI hgI

-- 導関数表記によるコロラリ（必要なら）
theorem integration_by_parts_deriv
  {f g : ℝ → ℝ} {a b : ℝ}
  (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (deriv f x) x)
  (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (deriv g x) x)
  (hfI : IntervalIntegrable (fun x => deriv f x) volume a b)
  (hgI : IntervalIntegrable (fun x => deriv g x) volume a b) :
  ∫ x in a..b, f x * deriv g x
    = f b * g b - f a * g a - ∫ x in a..b, deriv f x * g x := by
  simpa using integration_by_parts (f := f) (g := g)
    (f' := fun x => deriv f x) (g' := fun x => deriv g x)
    hf hg hfI hgI

-- ========= 動作確認用の簡単な例 =========
example : ∫ x in (0:ℝ)..(1:ℝ), x^2
    = ((1:ℝ)^(2+1) - (0:ℝ)^(2+1)) / (2 + 1) := by
  simpa using integral_pow' 2 0 1

example : ∫ x in (0:ℝ)..π, Real.sin x = 2 := by
  calc
    ∫ x in (0:ℝ)..π, Real.sin x
        = Real.cos 0 - Real.cos π := integral_sin' 0 π
    _ = 1 - (-1) := by simp [cos_zero, cos_pi]
    _ = 2 := by norm_num

end IntegralKadai

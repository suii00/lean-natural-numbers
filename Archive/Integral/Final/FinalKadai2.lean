import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Continuous
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Ring.Defs

/-!
Practical versions of the revised tasks:
- Concrete substitution example (exp ∘ (·)^2)
- Arctan integral
- Improper integral (tendsto) – scaffold
- Gaussian boundedness – scaffold
-/

noncomputable section

namespace FinalKadaiPractical

open Real intervalIntegral MeasureTheory

-- 課題1&2: 具体的置換例 ∫ 2x·e^{x²}
theorem integral_exp_squared_example (a b : ℝ) :
  ∫ x in a..b, 2 * x * Real.exp (x^2) = Real.exp (b^2) - Real.exp (a^2) := by
  -- F(x) = e^{x²}
  let F : ℝ → ℝ := fun x => Real.exp (x^2)
  have hF : ∀ x ∈ Set.uIcc a b,
      HasDerivAt F (2 * x * Real.exp (x^2)) x := by
    intro x _
    have hx2 : HasDerivAt (fun x : ℝ => x^2) (2 * x) x := by
      simpa [two_mul, pow_two] using (hasDerivAt_pow (n := 2) x)
    simpa [F, mul_comm, mul_left_comm, mul_assoc] using hx2.exp
  have hint : IntervalIntegrable (fun x : ℝ => 2 * x * Real.exp (x^2)) volume a b := by
    -- continuity ⇒ intervalIntegrable
    have hcont : Continuous (fun x : ℝ => (2 * x) * Real.exp (x^2)) := by
      have h1 : Continuous fun x : ℝ => 2 * x := continuous_const.mul continuous_id
      have h2 : Continuous fun x : ℝ => Real.exp (x^2) :=
        Real.continuous_exp.comp ((continuous_id : Continuous fun x : ℝ => x).pow 2)
      simpa [mul_comm] using h1.mul h2
    exact hcont.intervalIntegrable _ _
  simpa [F, mul_comm, mul_left_comm, mul_assoc] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint

-- 課題3: arctan の導関数の積分
theorem integral_arctan_derivative (a b : ℝ) :
  ∫ x in a..b, 1 / (1 + x^2) = Real.arctan b - Real.arctan a := by
  have hF : ∀ x ∈ Set.uIcc a b, HasDerivAt Real.arctan (1 / (1 + x^2)) x := by
    intro x _; simpa using Real.hasDerivAt_arctan x
  -- continuity ⇒ intervalIntegrable
  have hden : Continuous fun x : ℝ => 1 + x^2 :=
    continuous_const.add ((continuous_id : Continuous fun x : ℝ => x).pow 2)
  have hne : ∀ x : ℝ, 1 + x^2 ≠ 0 := by
    intro x
    have hx2 : 0 ≤ x^2 := by simpa using (sq_nonneg x)
    have : 0 < 1 + x^2 := by linarith
    exact ne_of_gt this
  have hcont : Continuous fun x : ℝ => 1 / (1 + x^2) := by
    -- 1 / (1 + x^2) = (1 + x^2)⁻¹
    simpa [one_div] using (hden.inv₀ hne)
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (1 + x^2)) volume a b :=
    hcont.intervalIntegrable _ _
  -- 直接等号を返して終了（linterの指摘も回避）
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  exact hFTC

-- 課題4: 部分分数分解による積分
-- 部分分数分解の補題
theorem integral_rational_decomposition :
  ∫ x in (1:ℝ)..(2:ℝ), 1 / (x * (x + 1)) =
  Real.log 2 - Real.log (3/2) := sorry


/- 課題5: 放物線 y = x² と直線 y = x で囲まれる面積
theorem area_between_curves :
  ∫ x in (0:ℝ)..(1:ℝ), (x - x^2) = 1/6 := by
  -- 線形性と ∫ x = 1/2, ∫ x^2 = 1/3 を用いる
  have I1 : ∫ x in (0:ℝ)..(1:ℝ), x = (1 : ℝ) / 2 := by
    have h := (integral_pow (1) (a := (0:ℝ)) (b := (1:ℝ)))
    -- ∫ x = (1^2 - 0^2)/2 = 1/2
    simpa [pow_one, one_div] using h
  have I2 : ∫ x in (0:ℝ)..(1:ℝ), x^2 = (1 : ℝ) / 3 := by
    have h := (integral_pow (2) (a := (0:ℝ)) (b := (1:ℝ)))
    -- ∫ x^2 = (1^3 - 0^3)/3 = 1/3
    have h' : (∫ x in (0:ℝ)..(1:ℝ), x ^ 2) = ((1:ℝ) ^ 3 - (0:ℝ) ^ 3) / 3 := by
      simpa using h
    simpa using h'
  have hxI : IntervalIntegrable (fun x : ℝ => x) volume (0:ℝ) (1:ℝ) :=
    (continuous_id : Continuous fun x : ℝ => x).intervalIntegrable _ _
  have hx2I : IntervalIntegrable (fun x : ℝ => x^2) volume (0:ℝ) (1:ℝ) :=
    ((continuous_id : Continuous fun x : ℝ => x).pow 2).intervalIntegrable _ _
  calc
    ∫ x in (0:ℝ)..(1:ℝ), (x - x^2)
        = ∫ x in (0:ℝ)..(1:ℝ), x + (-x^2) := by ring
    _ = (∫ x in (0:ℝ)..(1:ℝ), x) + (∫ x in (0:ℝ)..(1:ℝ), -x^2) := by
      simpa using intervalIntegral.integral_add hxI (hx2I.neg)
    _ = (∫ x in (0:ℝ)..(1:ℝ), x) - (∫ x in (0:ℝ)..(1:ℝ), x^2) := by simp
    _ = (1/2) - (1/3) := by simpa [I1, I2]
    _ = 1/6 := by norm_num


-- 課題6: y = √x を x軸周りに回転させた回転体の体積
theorem volume_of_revolution :
  Real.pi * ∫ x in (0:ℝ)..(1:ℝ), x = Real.pi / 2 := by
  -- V = π ∫₀¹ x dx, and ∫₀¹ x = 1/2
  have I1 : ∫ x in (0:ℝ)..(1:ℝ), x = (1 : ℝ) / 2 := by
    have h := (integral_pow (1) (a := (0:ℝ)) (b := (1:ℝ)))
    simpa [pow_one, one_div] using h
  calc
    Real.pi * (∫ x in (0:ℝ)..(1:ℝ), x)
        = Real.pi * ((1 : ℝ) / 2) := by simpa [I1]
    _ = Real.pi / 2 := by simpa using (mul_one_div Real.pi (2 : ℝ))



-- 課題7: 広義積分（tendsto 版）— 骨子（TODO）
/-
theorem improper_integral_simple :
  Filter.Tendsto (fun R : ℝ => ∫ x in (1:ℝ)..R, 1/x^2) Filter.atTop (𝓝 1) := by
  admit
-/

/- ガウス積分準備（簡略版）— 骨子（TODO）
theorem gaussian_bounded (R : ℝ) (hR : 0 < R) :
  0 < ∫ x in (-R)..R, Real.exp (-x^2) ∧
  ∫ x in (-R)..R, Real.exp (-x^2) ≤ 2 * R := by
  -- Nonnegativity and positivity
  have hpos_pt : ∀ x : ℝ, 0 < Real.exp (-x^2) := fun x => Real.exp_pos _
  have h_nonneg : ∀ x : ℝ, 0 ≤ Real.exp (-x^2) := fun x => (hpos_pt x).le
  -- Lower bound on a subinterval [0, r] with r = min R 1
  have hint_pos : 0 < ∫ x in (0:ℝ)..(min R 1), Real.exp (-x^2) := by
    -- simple bound: exp(-x^2) ≥ exp(-1) on [0,1]
    have hle1 : ∀ x ∈ Set.Icc (0:ℝ) (min R 1), -x^2 ≤ (0:ℝ) := by
      intro x hx; have hx2 : (0 : ℝ) ≤ x^2 := by nlinarith; linarith
    have hge_exp : ∀ x ∈ Set.Icc (0:ℝ) (min R 1), Real.exp (-x^2) ≥ Real.exp (-1) := by
      intro x hx
      have hxle : -1 ≤ -x^2 := by
        have hx01 : 0 ≤ x ∧ x ≤ 1 := by
          have hx0 : (0 : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
          have hx1 : x ≤ 1 := le_trans ((Set.mem_Icc.mp hx).2) (min_le_right _ _)
          exact ⟨hx0, hx1⟩
        have hx2 : x^2 ≤ 1 := by nlinarith [pow_two, hx01.2]
        have hx2' : -1 ≤ -x^2 := by linarith
        simpa using hx2'
      have : -x^2 ≤ 0 := by have := hle1 x hx; simpa using this
      -- exp is monotone; combine bounds carefully
      have : Real.exp (-x^2) ≥ Real.exp (-1) := by
        have hmono := Monotone.comp_right Real.exp_monotone id
        -- simpler: directly use monotonicity: -1 ≤ -x^2 → exp(-1) ≤ exp(-x^2)
        exact Real.exp_le_exp.mpr hxle |>.le
      exact this
    -- ∫ ≥ length * lower bound
    have hlen : 0 < (min R 1 - 0) := by
      have : 0 < min R 1 := lt_of_le_of_lt (by exact le_of_lt hR) (by norm_num)
      simpa using this
    -- Use a crude estimate: integral on [0,min R 1] is positive
    -- We avoid explicit constant factoring; positivity follows since integrand > 0 a.e.
    exact intervalIntegral.integral_pos_of_ae_pos measurableSet_Icc ?ae_nonneg ?ae_pos
  -- Upper bound: exp(-x^2) ≤ 1 ⇒ integral ≤ length = 2R
  have h_le_one : ∀ x : ℝ, Real.exp (-x^2) ≤ 1 := by
    intro x
    have hx2 : (0 : ℝ) ≤ x^2 := by nlinarith
    have : -x^2 ≤ 0 := by linarith
    simpa [Real.exp_zero] using (Real.exp_le_one_iff.mpr this)
  have hI1 : IntervalIntegrable (fun x : ℝ => Real.exp (-x^2)) volume (-R) R := by
    have hcont : Continuous fun x : ℝ => Real.exp (-(x^2)) :=
      Real.continuous_exp.comp (continuous_neg.comp ((continuous_id : Continuous fun x : ℝ => x).pow 2))
    exact hcont.intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (-R) R :=
    (continuous_const : Continuous fun _ : ℝ => (1:ℝ)).intervalIntegrable _ _
  have hmono : ∀ ⦃x⦄, x ∈ Set.Ioc (-R) R → Real.exp (-x^2) ≤ (1:ℝ) := by
    intro x hx; exact h_le_one x
  have h_bound : ∫ x in (-R)..R, Real.exp (-x^2) ≤ ∫ x in (-R)..R, (1:ℝ) := by
    exact intervalIntegral.integral_mono_of_nonneg (a := -R) (b := R) (μ := volume)
      (by intro x hx; exact (h_nonneg x)) hI1 hI2 (by intro x hx; exact h_le_one x)
  have h_len : ∫ x in (-R)..R, (1:ℝ) = (1:ℝ) * (R - (-R)) := by
    simpa [one_mul] using (intervalIntegral.integral_const (μ := volume) (a := -R) (b := R) (c := (1:ℝ)))
  have : ∫ x in (-R)..R, (1:ℝ) = 2 * R := by
    have : (R - (-R)) = 2 * R := by ring
    simpa [h_len, this]
  refine And.intro ?pos ?ub
  · -- strict positivity from hR and positivity on subinterval
    -- Simpler: since integrand > 0 and interval has positive length, integral > 0
    -- intervalIntegral has a lemma for this scenario
    have hpos_ae : (∂(volume)⟮Set.Ioc (-R) R⟯).AlmostEverywhere fun x => 0 < Real.exp (-x^2) := by
      exact Filter.eventually_of_forall (by intro x; exact hpos_pt x)
    have hlenpos : 0 < R - (-R) := by have : 0 < 2 * R := by nlinarith [hR]; simpa by ring
    -- use a known lemma: integral_pos_of_ae (nonneg & AE-pos on a set of positive measure)
    have : 0 < ∫ x in (-R)..R, Real.exp (-x^2) := by
      exact intervalIntegral.integral_pos_of_ae_nonneg_of_ae_pos (a := -R) (b := R)
        (by intro x hx; exact (h_nonneg x)) hpos_ae hlenpos
    exact this
  · -- upper bound
    simpa [this] using h_bound

#check ContinuousOn.inv₀
#check ContinuousWithinAt.inv₀
-/
end FinalKadaiPractical
-/

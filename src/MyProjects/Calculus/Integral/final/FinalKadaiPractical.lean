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
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

--author{CODEX (OpenAI)}
/-!
実用版の改訂課題のまとめ:
- 具体的置換の例（exp ∘ (·)^2）
- arctan の積分
- 広義積分（tendsto 版）の足場
- ガウス積分の有界性（足場）
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
    -- 連続性 ⇒ 区間可積分
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
  -- 連続性 ⇒ 区間可積分
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
/-課題4は、数学的には単純な部分分数だが、Lean では
領域・非零条件・集合（uIcc/Icc）の整合、
導関数の形と積分関数の一致のとり方（分解形か既約形か）、
自動化戦略（field_simp と simp の使い分け）
が絡み合うため難度が上がる。
-/

-- 課題5: 放物線 y = x² と直線 y = x で囲まれる面積
theorem area_between_curves :
  ∫ x in (0:ℝ)..(1:ℝ), (x - x^2) = 1/6 := by
  -- ∫₀¹ x = 1/2
  have I1 : ∫ x in (0:ℝ)..(1:ℝ), x = (1 : ℝ) / 2 := by
    simpa [pow_one, one_div] using
      (integral_pow (1) (a := (0:ℝ)) (b := (1:ℝ)))
  -- ∫₀¹ x^2 = 1/3（原始関数 F(x) = (1/3) x^3 を使う）
  have I2 : ∫ x in (0:ℝ)..(1:ℝ), x^2 = (1 : ℝ) / 3 := by
    let F : ℝ → ℝ := fun x => (1/3 : ℝ) * x^3
    have hF : ∀ x ∈ Set.uIcc (0:ℝ) (1:ℝ), HasDerivAt F (x^2) x := by
      intro x _
      have hx3 : HasDerivAt (fun x : ℝ => x^3) (3 * x^2) x := by
        simpa [pow_three] using (hasDerivAt_pow (n := 3) x)
      -- (1/3) * x^3 の導関数は (1/3) * (3 * x^2) = x^2
      simpa [F, one_div, mul_comm, mul_left_comm, mul_assoc] using hx3.const_mul (1/3 : ℝ)
    have hint2 : IntervalIntegrable (fun x : ℝ => x^2) volume (0:ℝ) (1:ℝ) :=
      ((continuous_id : Continuous fun x : ℝ => x).pow 2).intervalIntegrable _ _
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := (1:ℝ)) hF hint2
    simpa [F, one_div] using hFTC
  -- 可積分性（線形性のため）
  have hxI : IntervalIntegrable (fun x : ℝ => x) volume (0:ℝ) (1:ℝ) :=
    (continuous_id : Continuous fun x : ℝ => x).intervalIntegrable _ _
  have hx2I : IntervalIntegrable (fun x : ℝ => x^2) volume (0:ℝ) (1:ℝ) :=
    ((continuous_id : Continuous fun x : ℝ => x).pow 2).intervalIntegrable _ _
  calc
    ∫ x in (0:ℝ)..(1:ℝ), (x - x^2)
        = (∫ x in (0:ℝ)..(1:ℝ), x) - (∫ x in (0:ℝ)..(1:ℝ), x^2) := by
          simpa [sub_eq_add_neg] using
            (intervalIntegral.integral_sub (a := (0:ℝ)) (b := (1:ℝ)) (μ := volume) hxI hx2I)
    _ = (1/2) - (1/3) := by simpa [I1, I2]
    _ = 1/6 := by norm_num



-- 課題6: y = √x を x軸周りに回転させた回転体の体積
theorem volume_of_revolution :
  Real.pi * ∫ x in (0:ℝ)..(1:ℝ), x = Real.pi / 2 := by
  -- 体積 V = π ∫₀¹ x dx，かつ ∫₀¹ x = 1/2
  have I1 : ∫ x in (0:ℝ)..(1:ℝ), x = (1 : ℝ) / 2 := by
    have h := (integral_pow (1) (a := (0:ℝ)) (b := (1:ℝ)))
    simpa [pow_one, one_div] using h
  calc
    Real.pi * (∫ x in (0:ℝ)..(1:ℝ), x)
        = Real.pi * ((1 : ℝ) / 2) := by simpa [I1]
    _ = Real.pi / 2 := by simpa using (mul_one_div Real.pi (2 : ℝ))



-- 課題7: 広義積分（tendsto 版）
-- 補題: R ≥ 1 のときの評価 ∫₁^R 1/x^2 = 1 - 1/R
private lemma integral_one_div_sq_eval_of_le (R : ℝ) (hR : 1 ≤ R) :
  ∫ x in (1:ℝ)..R, 1 / x^2 = 1 - 1/R := by
  -- F(x) = - 1/x の導関数は 1/x^2（x ≠ 0 上）
  let F : ℝ → ℝ := fun x => - x⁻¹
  have hF : ∀ x ∈ Set.uIcc (1:ℝ) R, HasDerivAt F (1 / x^2) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (1:ℝ) R := by
      simpa [Set.uIcc_of_le hR] using hx
    have hx0 : x ≠ 0 := by
      have hx1 : (1:ℝ) ≤ x := (Set.mem_Icc.mp hxIcc).1
      have : 0 < x := lt_of_lt_of_le (by norm_num) hx1
      exact ne_of_gt this
    -- d/dx (-(1/x)) = 1/x^2 を示す
    have h_inv : HasDerivAt (fun x : ℝ => x⁻¹) (-(1) / x^2) x := by
      exact (hasDerivAt_id (x := x)).inv hx0
    -- neg を適用して -x⁻¹ の導関数を得る
    convert h_inv.neg using 1
    simp [F, one_div, neg_div, neg_neg]
    -- ringを削除（上のsimpで既に証明完了）

  -- 可積分性（閉区間上の連続性）
  have hint : IntervalIntegrable (fun x : ℝ => 1 / x^2) volume (1:ℝ) R := by
    -- 1/x^2 は [1,R] 上で連続（定数 ÷ 連続関数）
    have hconst : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.uIcc (1:ℝ) R) :=
      (continuous_const : Continuous fun _ : ℝ => (1:ℝ)).continuousOn
    have hsq : ContinuousOn (fun x : ℝ => x^2) (Set.uIcc (1:ℝ) R) :=
      ((continuous_id : Continuous fun x : ℝ => x).pow 2).continuousOn
    have hne : ∀ x ∈ Set.uIcc (1:ℝ) R, x^2 ≠ 0 := by
      intro x hx
      have hxIcc : x ∈ Set.Icc (1:ℝ) R := by simpa [Set.uIcc_of_le hR] using hx
      have hx1 : (1:ℝ) ≤ x := (Set.mem_Icc.mp hxIcc).1
      have hx0 : x ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le (by norm_num) hx1)
      exact pow_ne_zero 2 hx0
    have hcont_on : ContinuousOn (fun x : ℝ => (1:ℝ) / x^2) (Set.uIcc (1:ℝ) R) :=
      hconst.div hsq hne
    -- 連続（On）⇒ 区間可積分
    exact hcont_on.intervalIntegrable (a := (1:ℝ)) (b := R)

  -- 基本定理で評価
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (1:ℝ)) (b := R) hF hint
  simp only [F] at hFTC
  rw [hFTC]
  -- -R⁻¹ - (-1⁻¹) = 1 - R⁻¹ = 1 - 1/R を示す
  simp [div_eq_iff, mul_comm]
  ring

theorem improper_integral_simple :
  Filter.Tendsto (fun R : ℝ => ∫ x in (1:ℝ)..R, 1/x^2) Filter.atTop (nhds (1:ℝ)) := by
  -- R が十分大なら R ≥ 1 が成り立つ（atTop の性質）
  have h_ev : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ R := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨(1 : ℝ), ?_⟩
    intro R hR; exact hR

  -- 十分大での一致：∫₁^R 1/x^2 = 1 - 1/R
  have h_eq : (fun R : ℝ => ∫ x in (1:ℝ)..R, 1/x^2)
      =ᶠ[Filter.atTop] (fun R : ℝ => 1 - 1/R) :=
    h_ev.mono (by intro R hR; exact integral_one_div_sq_eval_of_le R hR)

  -- 右辺の極限：1 - 1/R → 1（R→∞ で 1/R → 0）
  have h_lim : Filter.Tendsto (fun R : ℝ => 1 - 1/R) Filter.atTop (nhds (1:ℝ)) := by
    have h_inv0 : Filter.Tendsto (fun R : ℝ => (1 : ℝ) / R) Filter.atTop (nhds (0:ℝ)) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    simpa using tendsto_const_nhds.sub h_inv0

  -- 最終的一致による極限の置換
  exact Filter.Tendsto.congr' h_eq.symm h_lim

-- 重複した定理定義を削除（200-216行目を削除）



-- ガウス積分準備（簡略版）— 骨子（TODO）
theorem gaussian_bounded (R : ℝ) (hR : 0 < R) :
  0 < ∫ x in (-R)..R, Real.exp (-x^2) ∧
  ∫ x in (-R)..R, Real.exp (-x^2) < 2 * Real.sqrt Real.pi := by
  -- AE（ほとんど至る所）を用いた正値性（区間 (−R, R)）
  have h_pos_pt : ∀ x : ℝ, 0 < Real.exp (-x^2) := fun x => Real.exp_pos _
  have h_nonneg_pt : ∀ x : ℝ, 0 ≤ Real.exp (-x^2) := fun x => (h_pos_pt x).le
  -- 正の部分区間 [0, r] と正の定数下界を用いて厳密正を示す
  set r : ℝ := min R 1
  have hr_pos : 0 < r := by
    have : 0 < R ∧ 0 < (1 : ℝ) := ⟨hR, by norm_num⟩
    simpa [r, lt_min_iff] using this
  -- 区間 [0, r] での可積分性
  have hcont : Continuous fun x : ℝ => Real.exp (-(x^2)) :=
    Real.continuous_exp.comp (continuous_neg.comp ((continuous_id : Continuous fun x : ℝ => x).pow 2))
  have hI_exp_sub : IntervalIntegrable (fun x : ℝ => Real.exp (-x^2)) volume (0:ℝ) r :=
    hcont.intervalIntegrable _ _
  have hI_const_sub : IntervalIntegrable (fun _ : ℝ => (Real.exp (-1) : ℝ)) volume (0:ℝ) r :=
    (continuous_const : Continuous fun _ : ℝ => (Real.exp (-1) : ℝ)).intervalIntegrable _ _
  -- 区間 [0, r] 上の点ごとの下界：exp(-1) ≤ exp(-x^2)
  have h_lower_on : ∀ ⦃x : ℝ⦄, x ∈ Set.Icc (0:ℝ) r → (Real.exp (-1) : ℝ) ≤ Real.exp (-(x^2)) := by
    intro x hx
    -- 0 ≤ x ≤ 1
    have hx0 : (0 : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
    have hx_le_r : x ≤ r := (Set.mem_Icc.mp hx).2
    have hx_le_one : x ≤ (1 : ℝ) := le_trans hx_le_r (min_le_right _ _)
    -- よって x^2 ≤ 1
    have hx2_le_one : x^2 ≤ (1 : ℝ) := by
      -- 0 ≤ x ≤ 1 から x^2 ≤ x，さらに x ≤ 1 より x^2 ≤ 1
      have hx_sq_le_x : x^2 ≤ x := by
        -- 0 ≤ x かつ x ≤ 1 なので x * x ≤ x * 1
        have : x * x ≤ x * (1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hx_le_one hx0
        simpa [pow_two, one_mul] using this
      exact le_trans hx_sq_le_x hx_le_one
    -- -1 ≤ -x^2 なので exp(-1) ≤ exp(-x^2)
    have hcmp : (-1 : ℝ) ≤ -x^2 := by
      simpa using (neg_le_neg hx2_le_one)
    simpa using (Real.exp_le_exp.mpr hcmp)
  -- 区間 [0, r] で積分を比較
  have h_sub_pos : 0 < ∫ x in (0:ℝ)..r, Real.exp (-x^2) := by
    -- Icc(0, r) 上の点wise単調性により ∫ 定数 ≤ ∫ exp(-x^2)
    have h_le := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := r) (μ := volume)
      (le_of_lt hr_pos) hI_const_sub hI_exp_sub (by intro x hx; exact h_lower_on hx)
    -- 左辺は (r - 0) * exp(-1)
    have h_const : ∫ x in (0:ℝ)..r, (Real.exp (-1) : ℝ)
        = (r - (0 : ℝ)) * (Real.exp (-1)) := by
      -- 定数関数の積分（integral_const）：(b - a) • c（実数では • = *）
      simpa using
        (intervalIntegral.integral_const (a := (0:ℝ)) (b := r) (c := (Real.exp (-1) : ℝ)))
    -- exp(-1) > 0 かつ r > 0 なので厳密に正
    have h_left_pos : 0 < ∫ x in (0:ℝ)..r, (Real.exp (-1) : ℝ) := by
      have hC : 0 < Real.exp (-1) := Real.exp_pos _
      have : 0 < (r - 0) * (Real.exp (-1)) := by
        have : 0 < r - 0 := by simpa using hr_pos
        exact mul_pos this hC
      simpa [h_const]
    exact lt_of_lt_of_le h_left_pos h_le
  -- 指示関数/AE 比較を用いて区間を [0, r] から [−R, R] へ拡大
  -- 集合の包含を示し，指示関数の AE 単調性を用いる
  have h_subset : Set.Ioc (0:ℝ) r ⊆ Set.Ioc (-R) R := by
    intro x hx
    have hx0 : 0 < x := (Set.mem_Ioc.mp hx).1
    have hxle : x ≤ r := (Set.mem_Ioc.mp hx).2
    have hxleR : x ≤ R := le_trans hxle (min_le_left _ _)
    have hgtmR : -R < x := lt_trans (neg_lt_zero.mpr hR) hx0
    exact ⟨hgtmR, hxleR⟩
  -- 両方の区間積分を，実数全体での指示関数の積分として書き換える
  have h_rewrite_big :
      ∫ x in (-R)..R, Real.exp (-x^2)
        = ∫ x, (Set.indicator (Set.Ioc (-R) R) fun x => Real.exp (-x^2)) x ∂volume := by
    have : ∫ x in (-R)..R, Real.exp (-x^2)
        = ∫ x, Real.exp (-x^2) ∂(volume.restrict (Set.Ioc (-R) R)) := by
      simpa using (intervalIntegral.integral_of_le (a := -R) (b := R)
        (f := fun x => Real.exp (-x^2)) (by linarith))
    simpa using (this.trans
      ((integral_indicator (μ := volume) (s := Set.Ioc (-R) R)
        (f := fun x : ℝ => Real.exp (-x^2)) (measurableSet_Ioc)).symm))
  have h_rewrite_small :
      ∫ x in (0:ℝ)..r, Real.exp (-x^2)
        = ∫ x, (Set.indicator (Set.Ioc (0:ℝ) r) fun x => Real.exp (-x^2)) x ∂volume := by
    have : ∫ x in (0:ℝ)..r, Real.exp (-x^2)
        = ∫ x, Real.exp (-x^2) ∂(volume.restrict (Set.Ioc (0:ℝ) r)) := by
      simpa using (intervalIntegral.integral_of_le (a := (0:ℝ)) (b := r)
        (f := fun x => Real.exp (-x^2)) (by exact (le_of_lt hr_pos)))
    simpa using (this.trans
      ((integral_indicator (μ := volume) (s := Set.Ioc (0:ℝ) r)
        (f := fun x : ℝ => Real.exp (-x^2)) (measurableSet_Ioc)).symm))
  -- 集合包含と非負性から指示関数の単調性を得る
  have h_ind_le : ∀ x : ℝ,
      (Set.indicator (Set.Ioc (0:ℝ) r) (fun x => Real.exp (-x^2)) x)
        ≤ (Set.indicator (Set.Ioc (-R) R) (fun x => Real.exp (-x^2)) x) := by
    intro x; by_cases hxS : x ∈ Set.Ioc (0:ℝ) r
    · have hxT : x ∈ Set.Ioc (-R) R := h_subset hxS
      simp [Set.indicator_of_mem hxS, Set.indicator_of_mem hxT]
    · by_cases hxT : x ∈ Set.Ioc (-R) R
      · have : 0 ≤ Real.exp (-x^2) := (Real.exp_pos _).le
        simp [Set.indicator_of_not_mem hxS, Set.indicator_of_mem hxT, this]
      · simp [Set.indicator_of_not_mem hxS, Set.indicator_of_not_mem hxT]
  -- 指示関数の2つの積分を比較（AE の単調性）
  have h_expand :
      ∫ x in (0:ℝ)..r, Real.exp (-x^2)
        ≤ ∫ x in (-R)..R, Real.exp (-x^2) := by  -- 区間拡大による比較（指示関数の AE 単調性で示す）
    -- いずれも体積測度に関する指示関数の積分として表す
    have h_big_int : Integrable (fun x : ℝ => (Set.indicator (Set.Ioc (-R) R)
      (fun x => Real.exp (-x^2)) x)) := by
      -- ガウス関数の可積分性から指示関数の可積分性を導く
      have h_gauss_int : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
        simpa [neg_mul, one_mul] using
          (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))
      exact h_gauss_int.indicator (measurableSet_Ioc)
    have h_small_int : Integrable (fun x : ℝ => (Set.indicator (Set.Ioc (0:ℝ) r)
      (fun x => Real.exp (-x^2)) x)) := by
      have h_gauss_int : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
        simpa [neg_mul, one_mul] using
          (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))
      exact h_gauss_int.indicator (measurableSet_Ioc)
    have hmono := MeasureTheory.integral_mono_ae h_small_int h_big_int
      (Filter.Eventually.of_forall (fun x => h_ind_le x))
    simpa [h_rewrite_small, h_rewrite_big]
      using hmono
  -- 最後に，大きい区間での厳密正
  have h_pos_integral : 0 < ∫ x in (-R)..R, Real.exp (-x^2) :=
    lt_of_lt_of_le h_sub_pos h_expand

  -- 全実線のガウス積分との AE 比較による上界（≤ √π < 2√π）
  have hle : (-R) ≤ R := by linarith
  -- 区間積分を制限測度に関する積分として書き換える
  have h_restrict :
      ∫ x in (-R)..R, Real.exp (-x^2)
        = ∫ x, Real.exp (-x^2) ∂(volume.restrict (Set.Ioc (-R) R)) := by
    simpa using (intervalIntegral.integral_of_le (a := -R) (b := R)
      (f := fun x => Real.exp (-x^2)) hle)

  -- 制限測度での積分を，実数全体での指示関数の積分に変換
  have h_indicator :
      ∫ x, Real.exp (-x^2) ∂(volume.restrict (Set.Ioc (-R) R))
        = ∫ x, (Set.indicator (Set.Ioc (-R) R) fun x => Real.exp (-x^2)) x ∂volume := by
    -- 制限測度と指示関数の標準的な同一視
    simpa using (integral_indicator (μ := volume)
      (s := Set.Ioc (-R) R) (f := fun x : ℝ => Real.exp (-x^2))
      (measurableSet_Ioc)).symm

  -- 点ごとの AE 不等式：被積分関数が非負なので indicator ≤ 本体
  have h_le_pt : ∀ x : ℝ, (Set.indicator (Set.Ioc (-R) R)
        (fun x => Real.exp (-x^2)) x) ≤ Real.exp (-x^2) := by
    intro x; by_cases hx : x ∈ Set.Ioc (-R) R
    · simp [Set.indicator_of_mem hx, h_nonneg_pt x]
    · simp [Set.indicator_of_not_mem hx, h_nonneg_pt x]

  -- 全実線でのガウス関数とその指示関数の可積分性
  have h_gauss_int : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
    -- 一般のガウス可積分性（b = 1）を利用
    simpa [neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))
  have h_gauss_int_indicator :
      Integrable (fun x => (Set.indicator (Set.Ioc (-R) R)
        (fun x => Real.exp (-x^2)) x)) :=
    h_gauss_int.indicator (measurableSet_Ioc)

  -- 指示関数の積分と全実線の積分を比較（AE 単調性）
  have h_bound_le :
      ∫ x, (Set.indicator (Set.Ioc (-R) R) fun x => Real.exp (-x^2)) x ∂volume
        ≤ ∫ x, Real.exp (-x^2) ∂volume := by
    refine MeasureTheory.integral_mono_ae h_gauss_int_indicator h_gauss_int ?_
    exact Filter.Eventually.of_forall (by intro x; exact h_le_pt x)

  -- 全実線でのガウス積分の値
  have h_gauss_val : ∫ x : ℝ, Real.exp (-x^2) = Real.sqrt Real.pi := by
    -- 一般のガウス積分を b = 1 に特殊化
    simpa [neg_mul, one_mul, div_one] using (integral_gaussian (b := (1 : ℝ)))

  -- 上界 < 2√π をまとめる
  have h_le_sqrtpi :
      ∫ x in (-R)..R, Real.exp (-x^2) ≤ Real.sqrt Real.pi := by
    have := calc
      ∫ x in (-R)..R, Real.exp (-x^2)
          = ∫ x, Real.exp (-x^2) ∂(volume.restrict (Set.Ioc (-R) R)) := h_restrict
      _ = ∫ x, (Set.indicator (Set.Ioc (-R) R) fun x => Real.exp (-x^2)) x ∂volume := h_indicator
      _ ≤ ∫ x, Real.exp (-x^2) ∂volume := h_bound_le
    simpa [h_gauss_val] using this

  have h_sqrtpi_pos : 0 < Real.sqrt Real.pi := by
    exact Real.sqrt_pos.mpr Real.pi_pos

  have h_upper : ∫ x in (-R)..R, Real.exp (-x^2) < 2 * Real.sqrt Real.pi := by
    have : Real.sqrt Real.pi < 2 * Real.sqrt Real.pi := by
      have h12 : (1 : ℝ) < 2 := by norm_num
      simpa [one_mul] using (mul_lt_mul_of_pos_right h12 h_sqrtpi_pos)
    exact lt_of_le_of_lt h_le_sqrtpi this

  exact And.intro h_pos_integral h_upper


end FinalKadaiPractical

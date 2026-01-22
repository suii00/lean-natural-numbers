/-
  ポリシリアル相関（Polyserial Correlation）のLean4形式化

  連続変数と順序カテゴリ変数の間の相関係数を定義する。
  潜在変数モデルに基づき、観測されるカテゴリの背後に
  連続的な潜在変数が存在すると仮定する。

  Explanation Pack (prototype, Bourbaki-style axiomatic layer)
  Purpose: provide a clean, set-theoretic interface for polyserial correlation,
  isolating analytic facts as explicit axioms until proofs are added.
  Main definitions:
  - OrdinalVariable: ordered categorical variable with k classes.
  - Thresholds: strictly increasing internal thresholds for categories.
  - LatentVariableModel: thresholds plus correlation parameter rho.
  - categoryProbability: P(Y = j | X = x) via normal CDF cut points.
  Main lemmas:
  - stdNormalPDF_nonneg: nonnegativity of the standard normal PDF.
  - categoryProbability_sum_eq_one: probabilities sum to 1.
  - polyserial_eq_biserial_when_k_eq_2: specialization to k = 2.
  Minimal example:
  - exampleThresholds3 and exampleModel demonstrate instantiation.
  Glossary:
  - rho: correlation parameter.
  - tau: threshold parameters.
-/

import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

noncomputable section

/-! ## 基本定義 -/

/-- 順序カテゴリ変数：k個のカテゴリを持つ -/
structure OrdinalVariable (k : ℕ) where
  value : Fin k
  deriving DecidableEq

/-- 閾値パラメータ：k個のカテゴリに対してk-1個の閾値
    τ₀ = -∞ < τ₁ < τ₂ < ... < τ_{k-1} < τ_k = +∞ -/
structure Thresholds (k : ℕ) where
  /-- 内部閾値 τ₁, ..., τ_{k-1} -/
  τ : Fin (k - 1) → ℝ
  /-- 閾値は狭義単調増加 -/
  strictly_increasing : StrictMono τ

/-- 拡張閾値：境界値 -∞ と +∞ を含む -/
def extendedThreshold {k : ℕ} (th : Thresholds k) (j : Fin (k + 1)) : EReal :=
  if h : j.val = 0 then ⊥  -- -∞
  else if h' : j.val = k then ⊤  -- +∞
  else (th.τ ⟨j.val - 1, by omega⟩ : EReal)

/-! ## 標準正規分布 -/

/-- 標準正規分布のPDF: φ(x) = (1/√(2π)) * exp(-x²/2) -/
def stdNormalPDF (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x^2) / 2)

/-- 標準正規分布のCDF: Φ(x) = ∫_{-∞}^{x} φ(t) dt -/
def stdNormalCDF (x : ℝ) : ℝ :=
  ∫ t in Iic x, stdNormalPDF t

/-! ## Axioms (Prototype) -/

namespace PolyserialAxioms

/-- Axiom: stdNormalPDF is nonnegative.
    What: stdNormalPDF x >= 0 for all x.
    Why: supports nonnegativity of probabilities and likelihoods.
    Technique: axiom placeholder; replace with mathlib proof.
-/
axiom Axiom_stdNormalPDF_nonneg (x : ℝ) : 0 ≤ stdNormalPDF x

/-- Axiom: stdNormalPDF integrates to 1 over ℝ.
    What: ∫ stdNormalPDF = 1.
    Why: normalization of the standard normal distribution.
    Technique: axiom placeholder; replace with mathlib proof.
-/
axiom Axiom_stdNormalPDF_integral_eq_one :
    ∫ x, stdNormalPDF x = 1

/-- Axiom: stdNormalCDF is monotone.
    What: stdNormalCDF is Monotone.
    Why: needed for interval probability bounds.
    Technique: axiom placeholder; replace with mathlib proof.
-/
axiom Axiom_stdNormalCDF_mono : Monotone stdNormalCDF

/-- Axiom: stdNormalCDF tends to 0 at -∞.
    What: lim_{x -> -∞} stdNormalCDF x = 0.
    Why: boundary behavior for tail probabilities.
    Technique: axiom placeholder; replace with mathlib proof.
-/
axiom Axiom_stdNormalCDF_tendsto_zero :
    Filter.Tendsto stdNormalCDF Filter.atBot (nhds 0)

/-- Axiom: stdNormalCDF tends to 1 at +∞.
    What: lim_{x -> +∞} stdNormalCDF x = 1.
    Why: boundary behavior for tail probabilities.
    Technique: axiom placeholder; replace with mathlib proof.
-/
axiom Axiom_stdNormalCDF_tendsto_one :
    Filter.Tendsto stdNormalCDF Filter.atTop (nhds 1)

end PolyserialAxioms

/-- φ(x) ≥ 0.
    What: stdNormalPDF x is nonnegative.
    Why: downstream nonnegativity of probabilities.
    Technique: by axiom placeholder.
-/
theorem stdNormalPDF_nonneg (x : ℝ) : 0 ≤ stdNormalPDF x := by
  simpa using PolyserialAxioms.Axiom_stdNormalPDF_nonneg x

/-- ∫_{-∞}^{+∞} φ(x) dx = 1.
    What: stdNormalPDF integrates to 1 on ℝ.
    Why: normalization of the standard normal distribution.
    Technique: by axiom placeholder.
-/
theorem stdNormalPDF_integral_eq_one :
    ∫ x, stdNormalPDF x = 1 := by
  simpa using PolyserialAxioms.Axiom_stdNormalPDF_integral_eq_one

/-- Φ is monotone.
    What: stdNormalCDF is Monotone.
    Why: used in probability bounds for intervals.
    Technique: by axiom placeholder.
-/
theorem stdNormalCDF_mono : Monotone stdNormalCDF := by
  simpa using PolyserialAxioms.Axiom_stdNormalCDF_mono

/-- lim_{x→-∞} Φ(x) = 0.
    What: stdNormalCDF tends to 0 at -∞.
    Why: boundary behavior for categorical cutoffs.
    Technique: by axiom placeholder.
-/
theorem stdNormalCDF_tendsto_zero :
    Filter.Tendsto stdNormalCDF Filter.atBot (nhds 0) := by
  simpa using PolyserialAxioms.Axiom_stdNormalCDF_tendsto_zero

/-- lim_{x→+∞} Φ(x) = 1.
    What: stdNormalCDF tends to 1 at +∞.
    Why: boundary behavior for categorical cutoffs.
    Technique: by axiom placeholder.
-/
theorem stdNormalCDF_tendsto_one :
    Filter.Tendsto stdNormalCDF Filter.atTop (nhds 1) := by
  simpa using PolyserialAxioms.Axiom_stdNormalCDF_tendsto_one

/-! ## 二変量正規分布 -/

/-- 二変量標準正規分布のPDF（相関係数ρ）-/
def bivariateNormalPDF (ρ : ℝ) (hρ : |ρ| < 1) (x y : ℝ) : ℝ :=
  let denom := 2 * Real.pi * Real.sqrt (1 - ρ^2)
  let exponent := -(x^2 - 2*ρ*x*y + y^2) / (2 * (1 - ρ^2))
  (1 / denom) * Real.exp exponent

namespace PolyserialAxioms

/-- Axiom: bivariate normal PDF integrates to 1.
    What: double integral of bivariateNormalPDF is 1.
    Why: normalization for the bivariate normal density.
    Technique: axiom placeholder; replace with mathlib proof.
-/
axiom Axiom_bivariateNormalPDF_integral_eq_one (ρ : ℝ) (hρ : |ρ| < 1) :
    ∫ x, ∫ y, bivariateNormalPDF ρ hρ x y = 1

end PolyserialAxioms

/-- 二変量正規分布は正規化されている。
    What: bivariateNormalPDF integrates to 1.
    Why: enables probabilistic interpretation of the density.
    Technique: by axiom placeholder.
-/
theorem bivariateNormalPDF_integral_eq_one (ρ : ℝ) (hρ : |ρ| < 1) :
    ∫ x, ∫ y, bivariateNormalPDF ρ hρ x y = 1 := by
  simpa using PolyserialAxioms.Axiom_bivariateNormalPDF_integral_eq_one ρ hρ

/-! ## 潜在変数モデル -/

/-- 潜在変数モデル：観測Y = j ⟺ τ_{j-1} < Y* ≤ τ_j -/
structure LatentVariableModel (k : ℕ) where
  /-- 閾値パラメータ -/
  thresholds : Thresholds k
  /-- 相関係数 ρ ∈ (-1, 1) -/
  ρ : ℝ
  /-- 相関係数の範囲制約 -/
  hρ : |ρ| < 1
  /-- カテゴリ数は2以上 -/
  hk : 1 < k

/-- カテゴリjに入る条件付き確率 P(Y = j | X = x) -/
def categoryProbability {k : ℕ} (model : LatentVariableModel k)
    (x : ℝ) (j : Fin k) : ℝ := by
  classical
  let σ := Real.sqrt (1 - model.ρ^2)
  have hk1 : 1 ≤ k := Nat.le_of_lt model.hk
  have hk0 : 0 < k - 1 := Nat.sub_pos_of_lt model.hk
  have upper_index : j.val + 1 < k → j.val < k - 1 := by
    intro h
    have h' : j.val + 1 < (k - 1) + 1 := by
      simpa [Nat.sub_add_cancel hk1] using h
    have h'' : j.val + 1 ≤ k - 1 := (Nat.lt_succ_iff.mp h')
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h''
  have lower_index : j.val > 0 → j.val - 1 < k - 1 := by
    intro h
    have hj1 : 1 ≤ j.val := (Nat.succ_le_iff.mpr h)
    exact Nat.sub_lt_sub_right hj1 j.isLt
  let upper := if h : j.val + 1 < k then
      (model.thresholds.τ ⟨j.val, upper_index h⟩ - model.ρ * x) / σ
    else 0  -- +∞ の場合、Φ(+∞) = 1 として処理
  let lower := if h : j.val > 0 then
      (model.thresholds.τ ⟨j.val - 1, lower_index h⟩ - model.ρ * x) / σ
    else 0  -- -∞ の場合、Φ(-∞) = 0 として処理
  exact if h0 : j.val = 0 then
    stdNormalCDF ((model.thresholds.τ ⟨0, hk0⟩ - model.ρ * x) / σ)
  else if hlast : j.val + 1 = k then
    1 - stdNormalCDF ((model.thresholds.τ ⟨j.val - 1, lower_index (Nat.pos_of_ne_zero h0)⟩
      - model.ρ * x) / σ)
  else
    stdNormalCDF upper - stdNormalCDF lower

namespace PolyserialAxioms

/-- Axiom: category probability is nonnegative.
    What: categoryProbability model x j >= 0.
    Why: ensures valid probabilities for each category.
    Technique: axiom placeholder; prove from CDF monotonicity.
-/
axiom Axiom_categoryProbability_nonneg {k : ℕ} (model : LatentVariableModel k)
    (x : ℝ) (j : Fin k) : 0 ≤ categoryProbability model x j

/-- Axiom: category probabilities sum to 1.
    What: sum_j categoryProbability model x j = 1.
    Why: total probability across categories.
    Technique: axiom placeholder; prove via telescoping CDF sum.
-/
axiom Axiom_categoryProbability_sum_eq_one {k : ℕ} (hk : 0 < k)
    (model : LatentVariableModel k) (x : ℝ) :
    ∑ j : Fin k, categoryProbability model x j = 1

end PolyserialAxioms

/-- カテゴリ確率は非負。
    What: categoryProbability is nonnegative.
    Why: required for likelihood nonnegativity.
    Technique: by axiom placeholder.
-/
theorem categoryProbability_nonneg {k : ℕ} (model : LatentVariableModel k)
    (x : ℝ) (j : Fin k) : 0 ≤ categoryProbability model x j := by
  simpa using PolyserialAxioms.Axiom_categoryProbability_nonneg model x j

/-- カテゴリ確率の総和は1。
    What: category probabilities sum to 1.
    Why: ensures a valid categorical distribution.
    Technique: by axiom placeholder.
-/
theorem categoryProbability_sum_eq_one {k : ℕ} (hk : 0 < k)
    (model : LatentVariableModel k) (x : ℝ) :
    ∑ j : Fin k, categoryProbability model x j = 1 := by
  simpa using PolyserialAxioms.Axiom_categoryProbability_sum_eq_one hk model x

/-! ## 尤度関数と最尤推定 -/

/-- 単一観測の尤度 -/
def singleLikelihood {k : ℕ} (model : LatentVariableModel k)
    (x : ℝ) (y : Fin k) : ℝ :=
  categoryProbability model x y * stdNormalPDF x

/-- サンプル全体の対数尤度関数 -/
def logLikelihood {k n : ℕ} (model : LatentVariableModel k)
    (data : Fin n → ℝ × Fin k) : ℝ :=
  ∑ i : Fin n, Real.log (singleLikelihood model (data i).1 (data i).2)

namespace PolyserialAxioms

/-- Axiom: choice of the MLE for polyserial correlation.
    What: a selected estimator value for each data set.
    Why: provides a placeholder for the MLE without constructing argmax.
    Technique: axiom placeholder; replace with existence/argmax construction.
-/
axiom Axiom_polyserialCorrelation {k n : ℕ} (data : Fin n → ℝ × Fin k) : ℝ

/-- Axiom: choice of the MLE for biserial correlation.
    What: a selected estimator value for k = 2 data.
    Why: needed for the k = 2 specialization lemma.
    Technique: axiom placeholder; replace with k = 2 construction.
-/
axiom Axiom_biserialCorrelation {n : ℕ} (data : Fin n → ℝ × Fin 2) : ℝ

end PolyserialAxioms

/-- ポリシリアル相関係数：最尤推定量。
    What: selected MLE value for the polyserial model.
    Why: central estimator used by consistency and asymptotic results.
    Technique: axiom placeholder via Axiom_polyserialCorrelation.
-/
def polyserialCorrelation {k n : ℕ} (data : Fin n → ℝ × Fin k) : ℝ :=
  PolyserialAxioms.Axiom_polyserialCorrelation data

/-- 二系列相関（k = 2 の最尤推定量）。
    What: biserial correlation estimator for k = 2.
    Why: comparison target for the k = 2 specialization lemma.
    Technique: axiom placeholder via Axiom_biserialCorrelation.
-/
def biserialCorrelation {n : ℕ} (data : Fin n → ℝ × Fin 2) : ℝ :=
  PolyserialAxioms.Axiom_biserialCorrelation data

namespace PolyserialAxioms

/-- Axiom: polyserial equals biserial when k = 2.
    What: polyserialCorrelation = biserialCorrelation for k = 2.
    Why: connects the general estimator to the classical special case.
    Technique: axiom placeholder; prove by specialization.
-/
axiom Axiom_polyserial_eq_biserial_when_k_eq_2 {n : ℕ}
    (data : Fin n → ℝ × Fin 2) :
    polyserialCorrelation data = biserialCorrelation data

end PolyserialAxioms

/-! ## 特殊ケース：二系列相関（Biserial Correlation） -/

/-- k = 2 の場合、ポリシリアル相関は二系列相関と一致。
    What: polyserialCorrelation = biserialCorrelation for k = 2.
    Why: validates the general definition against the known special case.
    Technique: by axiom placeholder.
-/
theorem polyserial_eq_biserial_when_k_eq_2 {n : ℕ}
    (data : Fin n → ℝ × Fin 2) :
    polyserialCorrelation data = biserialCorrelation data := by
  simpa using PolyserialAxioms.Axiom_polyserial_eq_biserial_when_k_eq_2 (data := data)

/-! ## 推定量の性質 -/

/-! ## Asymptotic behavior (placeholder predicates) -/

/-- Placeholder predicate for asymptotic normality.
    What: a Prop stating asymptotic normality for the estimator.
    Why: separates the probabilistic statement from its future formalization.
    Technique: axiom placeholder; replace with distributional convergence.
    Future: formalize √n (ρ̂_n - ρ) →^d N(0, 1 / I(ρ)) with Fisher information I(ρ).
-/
axiom AsymptoticallyNormal {k : ℕ} (model : LatentVariableModel k) : Prop

namespace PolyserialAxioms

/-- Axiom: consistency of the estimator.
    What: eventual closeness to the true rho for all data sets.
    Why: foundational asymptotic property for the estimator.
    Technique: axiom placeholder; prove in a probability theory layer.
    Note: this is deterministic; a probabilistic (measure-based) formulation is planned.
-/
axiom Axiom_polyserial_consistent {k : ℕ} (model : LatentVariableModel k) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ (data : Fin n → ℝ × Fin k),
      |polyserialCorrelation data - model.ρ| < ε

/-- Axiom: asymptotic normality of the estimator.
    What: AsymptoticallyNormal model holds.
    Why: supports asymptotic inference for the estimator.
    Technique: axiom placeholder; replace with a proof.
-/
axiom Axiom_polyserial_asymptotically_normal {k : ℕ} (model : LatentVariableModel k) :
    AsymptoticallyNormal model

end PolyserialAxioms

/-- 一致性：n → ∞ で真の値に収束。
    What: estimator converges to the true rho in the limit.
    Why: baseline statistical property for MLE.
    Technique: by axiom placeholder.
-/
theorem polyserial_consistent {k : ℕ} (model : LatentVariableModel k) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ (data : Fin n → ℝ × Fin k),
      |polyserialCorrelation data - model.ρ| < ε := by
  simpa using PolyserialAxioms.Axiom_polyserial_consistent model

/-- 漸近正規性。
    What: the estimator is asymptotically normal.
    Why: enables asymptotic confidence intervals and tests.
    Technique: by axiom placeholder.
-/
theorem polyserial_asymptotically_normal {k : ℕ} (model : LatentVariableModel k) :
    -- √n (ρ̂ - ρ) →^d N(0, σ²)
    AsymptoticallyNormal model := by
  simpa using PolyserialAxioms.Axiom_polyserial_asymptotically_normal model

/-! ## 具体例 -/

/-- 3カテゴリの順序変数（低・中・高）-/
example : OrdinalVariable 3 := ⟨⟨1, by norm_num⟩⟩  -- 「中」カテゴリ

/-- 3カテゴリ用の閾値例 -/
def exampleThresholds3 : Thresholds 3 where
  τ := fun i => if i.val = 0 then -1 else 1
  strictly_increasing := by
    intro i j hij
    simp only
    fin_cases i <;> fin_cases j <;> simp_all

/-- サンプルモデル -/
def exampleModel : LatentVariableModel 3 where
  thresholds := exampleThresholds3
  ρ := 0.5
  hρ := by norm_num
  hk := by norm_num

/-! ## 計算補助定理 -/

/-! ### 条件付き分布の性質（参考）
    二変量正規分布 (X, Y*) ~ BVN(0, 0, 1, 1, ρ) において：
    - E[Y* | X = x] = ρx
    - Var[Y* | X = x] = 1 - ρ²
    これらは categoryProbability の導出根拠となる。
    将来的に MeasureTheory.Probability での形式化を検討。
-/

namespace PolyserialAxioms

/-- Axiom: score function definition.
    What: definition of the score for rho.
    Why: used for Fisher information and asymptotic theory.
    Technique: axiom placeholder; define via derivatives of log-likelihood.
-/
axiom Axiom_scoreFunction {k : ℕ} (model : LatentVariableModel k)
    (x : ℝ) (y : Fin k) : ℝ

/-- Axiom: Fisher information definition.
    What: definition of Fisher information for rho.
    Why: needed for asymptotic variance statements.
    Technique: axiom placeholder; define via expectation.
-/
axiom Axiom_fisherInformation {k : ℕ} (model : LatentVariableModel k) : ℝ

/-- Axiom: Fisher information is positive.
    What: Axiom_fisherInformation model > 0.
    Why: ensures non-degenerate asymptotic variance.
    Technique: axiom placeholder; prove under regularity conditions.
-/
axiom Axiom_fisherInformation_pos {k : ℕ} (model : LatentVariableModel k) :
    0 < Axiom_fisherInformation model

end PolyserialAxioms

/-- スコア関数（ρに関する対数尤度の微分）。
    What: score function for rho at a single observation.
    Why: building block for Fisher information.
    Technique: axiom placeholder via Axiom_scoreFunction.
-/
def scoreFunction {k : ℕ} (model : LatentVariableModel k)
    (x : ℝ) (y : Fin k) : ℝ :=
  -- ∂/∂ρ log P(Y = y | X = x)
  PolyserialAxioms.Axiom_scoreFunction model x y

/-- フィッシャー情報量。
    What: Fisher information for rho in the model.
    Why: drives asymptotic variance of the estimator.
    Technique: axiom placeholder via Axiom_fisherInformation.
-/
def fisherInformation {k : ℕ} (model : LatentVariableModel k) : ℝ :=
  -- E[(∂/∂ρ log L)²]
  PolyserialAxioms.Axiom_fisherInformation model

/-- フィッシャー情報量は正。
    What: fisherInformation model > 0.
    Why: ensures non-degenerate information.
    Technique: by axiom placeholder.
-/
theorem fisherInformation_pos {k : ℕ} (model : LatentVariableModel k) :
    0 < fisherInformation model := by
  simpa [fisherInformation] using PolyserialAxioms.Axiom_fisherInformation_pos model

end

/-! ## 注釈

### 形式化のポイント
1. 順序カテゴリ変数を `Fin k` で表現
2. 閾値は狭義単調増加の制約付き
3. 潜在変数モデルは相関係数と閾値をパラメータとして保持
4. カテゴリ確率は条件付き正規分布から導出

### Mathlib4との対応
- `stdNormalPDF` / `stdNormalCDF` : Mathlib4の正規分布モジュールと整合
- 測度論的確率論の枠組みで厳密化可能
- 実際の証明には `MeasureTheory.Probability` の活用が必要

### 拡張の方向性
- ポリコリック相関（両変数が順序カテゴリ）への一般化
- 欠測データの処理
- ベイズ推定版の定式化
-/

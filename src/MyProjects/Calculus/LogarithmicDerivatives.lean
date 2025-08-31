import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Basic

namespace LogarithmicDerivatives

open Real Filter Topology

-- ========= パート1: 対数関数の基本微分 =========

-- 課題1: log(x)の微分は1/x（x > 0）
theorem log_deriv_basic (x : ℝ) (_ : 0 < x) :
  deriv Real.log x = 1 / x := by
  rw [Real.deriv_log x]
  rw [inv_eq_one_div]

-- 課題2: log(ax)の微分は1/x（aは正の定数）
theorem log_ax_deriv (a : ℝ) (ha : 0 < a) :
  ∀ x : ℝ, 0 < x → deriv (fun x => Real.log (a * x)) x = 1 / x := by
  intro x hx
  -- 連鎖律を使用
  have h1 : HasDerivAt (fun x => a * x) a x := by
    convert (hasDerivAt_id' x).const_mul a using 1
    simp
  have h2 : 0 < a * x := mul_pos ha hx
  have h3 : HasDerivAt Real.log (a * x)⁻¹ (a * x) := 
    Real.hasDerivAt_log h2.ne'
  have h4 : HasDerivAt (fun x => Real.log (a * x)) ((a * x)⁻¹ * a) x :=
    HasDerivAt.comp x h3 h1
  rw [HasDerivAt.deriv h4]
  field_simp

-- 課題3: log(x²+1)の微分（連鎖律の応用）
theorem log_quadratic_deriv :
  ∀ x : ℝ, deriv (fun x => Real.log (x^2 + 1)) x = 2 * x / (x^2 + 1) := by
  intro x
  -- x²+1 > 0は常に成立
  have hpos : 0 < x^2 + 1 := by
    apply add_pos_of_nonneg_of_pos
    · exact sq_nonneg x
    · norm_num
  -- 連鎖律適用
  have h1 : HasDerivAt (fun x => x^2 + 1) (2 * x) x := by
    convert (hasDerivAt_pow 2 x).add (hasDerivAt_const x 1) using 1
    ring
  have h2 : HasDerivAt Real.log (x^2 + 1)⁻¹ (x^2 + 1) :=
    Real.hasDerivAt_log hpos.ne'
  -- 連鎖律で合成
  have h3 : HasDerivAt (fun x => Real.log (x^2 + 1)) ((x^2 + 1)⁻¹ * (2 * x)) x := by
    convert HasDerivAt.comp x h2 h1 using 1
  rw [HasDerivAt.deriv h3]
  simp only [inv_eq_one_div]
  ring

-- ========= パート2: 逆関数の微分 =========

-- 課題4: e^(log x) = x の微分的確認
theorem exp_log_deriv (x : ℝ) (hx : 0 < x) :
  deriv (fun x => Real.exp (Real.log x)) x = 1 := by
  -- e^(log x) = x の性質を利用
  -- 関数がxで恒等関数と等しい
  have : ∀ᶠ z in 𝓝 x, Real.exp (Real.log z) = z := by
    filter_upwards [eventually_gt_nhds hx] with z hz
    exact exp_log hz
  -- 恒等関数と局所的に等しいなら微分も等しい
  have eq : deriv (fun x => Real.exp (Real.log x)) x = deriv id x := by
    apply Filter.EventuallyEq.deriv_eq
    exact this
  rw [eq]
  rw [deriv_id]

-- 課題5: log(e^x) = x の微分的確認
theorem log_exp_deriv :
  ∀ x : ℝ, deriv (fun x => Real.log (Real.exp x)) x = 1 := by
  intro x
  -- log(e^x) = x の性質を利用
  -- 関数が恒等関数と等しい
  have : (fun x => Real.log (Real.exp x)) = id := by
    ext z
    simp only [id, log_exp z]
  rw [this]
  rw [deriv_id]

-- ========= パート3: 一般の対数関数 =========

-- 課題6: log_a(x) = log(x)/log(a) の微分
theorem log_base_deriv (a : ℝ) (ha : 0 < a) (ha' : a ≠ 1) :
  ∀ x : ℝ, 0 < x → 
  deriv (fun x => Real.log x / Real.log a) x = 1 / (x * Real.log a) := by
  intro x _
  -- 定数での割り算の微分
  have hlog_a : Real.log a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ha ha'
  rw [deriv_div_const _]
  rw [Real.deriv_log x]
  field_simp

-- ========= チャレンジ: 逆関数の微分公式 =========

-- 逆関数の微分定理の具体例
theorem inverse_function_deriv_example :
  ∀ y : ℝ, 0 < y → 
  deriv Real.log y = 1 / deriv Real.exp (Real.log y) := by
  intro y hy
  -- log'(y) = 1/y, exp'(log y) = exp(log y) = y
  rw [Real.deriv_log y]
  rw [Real.deriv_exp]
  rw [exp_log hy]
  rw [inv_eq_one_div]

-- 応用: x * log(x) の微分（積の法則と対数微分）
theorem x_log_x_deriv (x : ℝ) (hx : 0 < x) :
  deriv (fun x => x * Real.log x) x = Real.log x + 1 := by
  -- 積の微分法則を適用
  have h1 : HasDerivAt (fun x => x) 1 x := hasDerivAt_id' x
  have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h3 : HasDerivAt (fun x => x * Real.log x) (1 * Real.log x + x * x⁻¹) x :=
    HasDerivAt.mul h1 h2
  rw [HasDerivAt.deriv h3]
  field_simp

end LogarithmicDerivatives
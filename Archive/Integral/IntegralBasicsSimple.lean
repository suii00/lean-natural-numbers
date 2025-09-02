import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace IntegralBasicsSimple

open Real intervalIntegral

-- ========= 基本的な積分公式の確認 =========

-- 定数関数の積分
example (c a b : ℝ) : 
  ∫ x in a..b, c = (b - a) • c := by
  exact intervalIntegral.integral_const

-- べき関数の積分
example (n : ℕ) (a b : ℝ) :
  ∫ x in a..b, x^n = (b^(n+1) - a^(n+1)) / (n + 1) := by
  exact integral_pow n

-- 正弦関数の積分
example (a b : ℝ) :
  ∫ x in a..b, sin x = cos a - cos b := by
  exact integral_sin

-- 余弦関数の積分
example (a b : ℝ) :
  ∫ x in a..b, cos x = sin b - sin a := by
  exact integral_cos

-- ========= 具体的な計算例 =========

-- x の積分（0から1）
example : ∫ x in (0:ℝ)..(1:ℝ), x = 1/2 := by
  rw [integral_pow 1]
  norm_num

-- 定数の積分
example : ∫ x in (0:ℝ)..(2:ℝ), 3 = 6 := by
  rw [intervalIntegral.integral_const]
  norm_num

-- x² の積分（0から1）
example : ∫ x in (0:ℝ)..(1:ℝ), x^2 = 1/3 := by
  rw [integral_pow 2]
  norm_num

-- sin の積分（0からπ）
example : ∫ x in (0:ℝ)..π, sin x = 2 := by
  rw [integral_sin]
  simp [cos_zero, cos_pi]

end IntegralBasicsSimple
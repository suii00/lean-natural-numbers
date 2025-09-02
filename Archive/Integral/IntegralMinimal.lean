import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace IntegralMinimal

open Real intervalIntegral

-- ========= 最小限の動作確認 =========

-- 基本的な公式そのもの
#check integral_pow
#check integral_sin 
#check integral_cos

-- 最もシンプルな使用例
example : ∫ x in (0:ℝ)..(1:ℝ), x^2 = 1/3 := by
  rw [integral_pow 2]
  simp [pow_succ, pow_zero]
  norm_num

example : ∫ x in (0:ℝ)..π, sin x = 2 := by
  rw [integral_sin]
  simp [cos_zero, cos_pi]

-- x の積分（x = x^1 として）
example : ∫ x in (0:ℝ)..(1:ℝ), x = 1/2 := by  
  conv_lhs => rw [← pow_one (x)]
  rw [integral_pow 1]
  simp [pow_succ, pow_zero]
  norm_num

-- より高次の例
example : ∫ x in (0:ℝ)..(1:ℝ), x^4 = 1/5 := by
  rw [integral_pow 4]
  simp [pow_succ, pow_zero]
  norm_num

-- 区間を変えた例  
example : ∫ x in (0:ℝ)..(2:ℝ), x^2 = 8/3 := by
  rw [integral_pow 2]
  simp [pow_succ, pow_zero]
  norm_num

-- ========= claude.txtの課題に対応 =========

-- 課題1相当: 定数（x^0として実装）
theorem integral_one (a b : ℝ) : ∫ x in a..b, 1 = b - a := by
  conv_lhs => rw [← pow_zero (x : ℝ)]
  rw [integral_pow 0]
  simp [pow_one, pow_zero]

-- 課題2: べき関数
theorem integral_power (n : ℕ) (a b : ℝ) :
  ∫ x in a..b, x^n = (b^(n+1) - a^(n+1)) / (n + 1) := 
integral_pow n

-- 課題3: 三角関数  
theorem integral_sine (a b : ℝ) :
  ∫ x in a..b, sin x = cos a - cos b := 
integral_sin

theorem integral_cosine (a b : ℝ) :
  ∫ x in a..b, cos x = sin b - sin a := 
integral_cos

end IntegralMinimal
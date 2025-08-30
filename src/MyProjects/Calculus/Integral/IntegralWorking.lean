import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace IntegralWorking

open Real

-- 積分記号の明示的使用 
open intervalIntegral

-- ========= 基本的な積分の動作確認 =========

-- べき関数の積分（最初に動作するもの）
example (n : ℕ) (a b : ℝ) :
  ∫ x in a..b, x^n = (b^(n+1) - a^(n+1)) / (n + 1) := 
integral_pow n

-- 三角関数の積分
example (a b : ℝ) :
  ∫ x in a..b, sin x = cos a - cos b := 
integral_sin

example (a b : ℝ) :
  ∫ x in a..b, cos x = sin b - sin a := 
integral_cos

-- ========= 具体的な数値例（慎重にテスト） =========

-- まず一番シンプルな例
example : ∫ x in (0:ℝ)..(1:ℝ), x = 1/2 := by
  calc ∫ x in (0:ℝ)..(1:ℝ), x 
    = ∫ x in (0:ℝ)..(1:ℝ), x^1 := by simp [pow_one]
    _ = ((1:ℝ)^(1+1) - (0:ℝ)^(1+1)) / (1 + 1) := integral_pow 1
    _ = (1 - 0) / 2 := by norm_num
    _ = 1/2 := by norm_num

-- x²の積分
example : ∫ x in (0:ℝ)..(1:ℝ), x^2 = 1/3 := by
  calc ∫ x in (0:ℝ)..(1:ℝ), x^2 
    = (1^(2+1) - 0^(2+1)) / (2 + 1) := integral_pow 2
    _ = (1 - 0) / 3 := by norm_num
    _ = 1/3 := by norm_num

-- 三角関数の例
example : ∫ x in (0:ℝ)..π, sin x = 2 := by
  calc ∫ x in (0:ℝ)..π, sin x 
    = cos 0 - cos π := integral_sin
    _ = 1 - (-1) := by simp [cos_zero, cos_pi]
    _ = 2 := by norm_num

-- ========= 面積計算の例 =========

-- 放物線 y = x²の面積 (0 ≤ x ≤ 1)
theorem area_under_parabola : ∫ x in (0:ℝ)..(1:ℝ), x^2 = 1/3 := by
  calc ∫ x in (0:ℝ)..(1:ℝ), x^2 
    = (1^(2+1) - 0^(2+1)) / (2 + 1) := integral_pow 2
    _ = 1/3 := by norm_num

-- より一般的な例 x^3
example : ∫ x in (0:ℝ)..(2:ℝ), x^3 = 4 := by
  calc ∫ x in (0:ℝ)..(2:ℝ), x^3 
    = (2^(3+1) - 0^(3+1)) / (3 + 1) := integral_pow 3
    _ = 16 / 4 := by norm_num
    _ = 4 := by norm_num

-- ========= 教育的な段階的例 =========

-- ステップ1: 定数（別のアプローチが必要）
-- 定数積分は型の問題があるため、べき関数として扱う
theorem constant_as_power : ∫ x in (a:ℝ)..b, 1 = b - a := by
  calc ∫ x in a..b, 1 
    = ∫ x in a..b, x^0 := by simp [pow_zero]
    _ = (b^(0+1) - a^(0+1)) / (0 + 1) := integral_pow 0
    _ = (b - a) / 1 := by simp [pow_one]
    _ = b - a := by simp

-- ステップ2: 線形関数
theorem linear_function : ∫ x in (0:ℝ)..(2:ℝ), x = 2 := by
  calc ∫ x in (0:ℝ)..(2:ℝ), x 
    = (2^2 - 0^2) / 2 := integral_pow 1
    _ = 4 / 2 := by norm_num
    _ = 2 := by norm_num

-- ステップ3: より高次
theorem quartic_function : ∫ x in (0:ℝ)..(1:ℝ), x^4 = 1/5 := by
  calc ∫ x in (0:ℝ)..(1:ℝ), x^4 
    = (1^5 - 0^5) / 5 := integral_pow 4
    _ = 1/5 := by norm_num

-- ========= 微分積分学の基本定理の概念 =========

-- 概念: d/dx ∫[a to x] f(t) dt = f(x) のイメージ
-- これは別ファイルで詳細実装予定

/-- 
積分と微分の逆関係の概念的理解:
- ∫ f'(x) dx = f(x) + C
- d/dx ∫[a to x] f(t) dt = f(x)

この関係により、積分は「面積を求める操作」であると同時に
「微分の逆演算」でもあることがわかる。
-/

end IntegralWorking
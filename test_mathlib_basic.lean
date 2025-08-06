-- Mathlib基本機能テスト
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- 基本的な自然数の証明
example : 2 + 2 = 4 := by norm_num

-- 偶数の証明（mathlibの使用）
example : Even 4 := by
  use 2
  norm_num

-- ringタクティクのテスト  
example (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by ring

-- omegaタクティクのテスト
example (n : ℕ) : n + 0 = n := by omega

#check Nat.even_iff_exists_two_nsmul
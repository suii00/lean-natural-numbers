import Mathlib.Data.Int.Basic
import Mathlib.Tactic

-- Module: SquareEven.Working
-- 「平方が偶数なら元の数も偶数」定理の現代的Lean 4証明
namespace SquareEven

-- ステップ1: Mathlib標準の偶数定義を使用
-- Even n ↔ ∃ k, n = 2 * k (Mathlibに既に定義済み)

-- ステップ2: 定義を直接利用（Mathlibでは定義済み）
-- Even n と Odd n の定義をそのまま使用

-- ステップ4: 基本補題 - 偶数の平方は偶数
lemma even_square (n : ℤ) : Even n → Even (n * n) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 2 * k * k
  rw [hk]
  ring

-- ステップ5: 奇数の平方は奇数
lemma odd_square (n : ℤ) : Odd n → Odd (n * n) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 2 * k * k + 2 * k
  rw [hk]
  ring

-- ステップ6: メイン定理 - 平方が偶数なら元も偶数
theorem square_even_main (n : ℤ) : Even (n * n) → Even n := by
  contrapose
  intro h
  -- nが偶数でない → nは奇数（整数の分類）
  have h_odd : Odd n := by
    -- 整数は偶数か奇数
    cases' Int.even_or_odd n with h_even h_odd
    · contradiction
    · exact h_odd
  -- 奇数の平方は奇数
  have h_square_odd : Odd (n * n) := odd_square n h_odd
  -- 奇数は偶数でない
  intro h_even_square
  -- 平方が偶数かつ奇数で矛盾
  exact Int.not_even_iff_odd.mpr h_square_odd h_even_square

end SquareEven
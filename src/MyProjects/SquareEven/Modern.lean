import Mathlib.Data.Int.Basic
import Mathlib.Tactic

-- Module: SquareEven.Modern
-- 「平方が偶数なら元の数も偶数」定理の完全証明（Mathlib 4対応）
namespace SquareEven

-- 基本補題1: 偶数の平方は偶数
lemma even_square (n : ℤ) : Even n → Even (n * n) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 2 * k * k
  rw [hk]
  ring

-- 基本補題2: 奇数の平方は奇数
lemma odd_square (n : ℤ) : Odd n → Odd (n * n) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 2 * k * k + 2 * k
  rw [hk]
  ring

-- メイン定理: 平方が偶数なら元の数も偶数
theorem square_even_implies_even (n : ℤ) : Even (n * n) → Even n := by
  contrapose
  intro h_not_even
  -- 整数の完全分類: 偶数でない → 奇数
  have h_odd : Odd n := by
    cases' Int.even_or_odd n with h_even h_odd
    · contradiction
    · exact h_odd
  -- 奇数の平方は奇数
  have h_square_odd : Odd (n * n) := odd_square n h_odd
  -- 奇数は偶数でない
  intro h_even_square
  exact Int.not_even_iff_odd.mpr h_square_odd h_even_square

-- 逆方向も証明: 偶数なら平方も偶数
theorem even_implies_square_even (n : ℤ) : Even n → Even (n * n) := 
  even_square n

-- 同値性定理
theorem square_even_iff_even (n : ℤ) : Even (n * n) ↔ Even n := by
  constructor
  · exact square_even_implies_even n
  · exact even_implies_square_even n

-- 具体例での検証
example : Even ((4 : ℤ) * 4) := by
  have h : Even (4 : ℤ) := ⟨2, by norm_num⟩
  exact even_square 4 h

example : Even ((-6 : ℤ) * (-6)) := by
  have h : Even (-6 : ℤ) := ⟨-3, by norm_num⟩
  exact even_square (-6) h

-- 対偶も検証  
example : Odd (5 : ℤ) → Odd ((5 : ℤ) * 5) := odd_square 5

example : Odd ((5 : ℤ) * 5) := by
  have h : Odd (5 : ℤ) := ⟨2, by norm_num⟩
  exact odd_square 5 h

-- 最終形: 整数の平方とパリティの関係
theorem integer_square_parity_summary (n : ℤ) :
  Even n ↔ Even (n * n) := (square_even_iff_even n).symm

-- 対偶形（一方向のみ証明）
theorem odd_implies_odd_square (n : ℤ) : Odd n → Odd (n * n) := odd_square n

-- 核心的結論
theorem main_result (n : ℤ) : Even (n * n) → Even n := square_even_implies_even n

end SquareEven
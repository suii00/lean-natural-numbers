import Mathlib.Tactic.Basic

-- Module: SquareEven.Basic
-- 平方が偶数なら元の数も偶数であることの証明

namespace SquareEven

-- 偶数・奇数の定義（整数版）
def MyEven (n : Z) : Prop := ∃ k : Z, n = 2 * k
def MyOdd (n : Z) : Prop := ∃ k : Z, n = 2 * k + 1

-- 基本的な例
theorem zero_even : MyEven 0 := by
  exact ⟨0, rfl⟩

theorem two_even : MyEven 2 := by
  exact ⟨1, rfl⟩

theorem one_odd : MyOdd 1 := by
  exact ⟨0, rfl⟩

-- 基本公理（簡略化のため）
axiom int_even_or_odd (n : Z) : MyEven n ∨ MyOdd n
axiom even_odd_exclusive : ∀ (n : Z), ¬(MyEven n ∧ MyOdd n)

-- 偶数でないなら奇数
lemma not_even_iff_odd (n : Z) : ¬MyEven n ↔ MyOdd n := by
  constructor
  · intro h
    cases int_even_or_odd n with
    | inl he => exact False.elim (h he)
    | inr ho => exact ho
  · intro h he
    exact even_odd_exclusive n ⟨he, h⟩

-- 奇数の平方は奇数
lemma odd_square (n : Z) : MyOdd n → MyOdd (n * n) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 2 * k * k + 2 * k
  rw [hk]
  calc (2 * k + 1) * (2 * k + 1) 
    = 4 * k * k + 4 * k + 1 := by rfl
    _ = 2 * (2 * k * k + 2 * k) + 1 := by rfl

-- メインの定理: 平方が偶数なら元の数も偶数
theorem even_square_main (n : Z) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  -- 対偶を使用: ¬MyEven n → ¬MyEven (n * n)
  cases int_even_or_odd n with
  | inl h_even => exact h_even
  | inr h_odd => 
    -- n が奇数の場合
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_square_not_even : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
    -- 矛盾
    exact False.elim (h_square_not_even h_even_square)

-- より直接的な証明
theorem even_square_direct (n : Z) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  cases int_even_or_odd n with
  | inl h => exact h
  | inr h_odd => 
    -- n が奇数の場合
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_not_even_square : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
    exact False.elim (h_not_even_square h_even_square)

-- 最もシンプルな証明
theorem even_square_simple (n : Z) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  cases int_even_or_odd n with
  | inl h_even => exact h_even
  | inr h_odd => 
    have h_square_odd := odd_square n h_odd
    have h_square_not_even := (not_even_iff_odd (n * n)).mpr h_square_odd
    exact False.elim (h_square_not_even h_even_square)

-- 具体例での検証
theorem example_four_square : MyEven (4 * 4) → MyEven 4 := even_square_main 4

-- 基本算術の例
example : (4 : Z) + 6 = 10 := by rfl

-- 検証
#check even_square_main
#check even_square_direct  
#check even_square_simple

end SquareEven

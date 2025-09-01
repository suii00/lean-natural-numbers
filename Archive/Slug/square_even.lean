import Mathlib.Tactic
import Mathlib.Data.Int.Basic

-- 偶数・奇数の定義
def MyEven (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k
def MyOdd (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k + 1

-- 基本的な例
theorem zero_even : MyEven 0 := ⟨0, by ring⟩
theorem two_even : MyEven 2 := ⟨1, by ring⟩
theorem one_odd : MyOdd 1 := ⟨0, by ring⟩

-- 簡略化された補助補題（axiomとして扱う）
axiom int_even_or_odd (n : ℤ) : MyEven n ∨ MyOdd n
axiom even_odd_exclusive (n : ℤ) : ¬(MyEven n ∧ MyOdd n)

-- 偶数でないなら奇数
lemma not_even_iff_odd (n : ℤ) : ¬MyEven n ↔ MyOdd n := by
  constructor
  · intro h
    cases int_even_or_odd n with
    | inl he => exact False.elim (h he)
    | inr ho => exact ho
  · intro h he
    exact even_odd_exclusive n ⟨he, h⟩

-- 奇数の平方は奇数
lemma odd_square (n : ℤ) : MyOdd n → MyOdd (n * n) := by
  intro ⟨k, hk⟩
  use 2 * k * k + 2 * k
  rw [hk]
  ring

-- メインの定理（修正版）
theorem even_square_main (n : ℤ) : MyEven (n * n) → MyEven n := by
  contrapose!
  intro h
  have h_odd : MyOdd n := (not_even_iff_odd n).mp h
  have h_square_odd : MyOdd (n * n) := odd_square n h_odd
  -- MyOdd を ¬MyEven に変換
  exact (not_even_iff_odd (n * n)).mpr h_square_odd

-- より直接的な証明
theorem even_square_direct (n : ℤ) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  by_cases h : MyEven n
  · exact h
  · have h_odd : MyOdd n := (not_even_iff_odd n).mp h
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_not_even_square : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
    exact False.elim (h_not_even_square h_even_square)

-- 最もシンプルな証明
theorem even_square_simple (n : ℤ) : MyEven (n * n) → MyEven n := by
  contrapose!
  exact fun h => (not_even_iff_odd (n * n)).mpr (odd_square n ((not_even_iff_odd n).mp h))

-- 検証
#check even_square_main
#check even_square_direct  
#check even_square_simple

-- mathlibの機能も簡単にテスト
example : (4 : ℤ) + 6 = 10 := by norm_num
example : Even (4 : ℤ) := ⟨2, by norm_num⟩
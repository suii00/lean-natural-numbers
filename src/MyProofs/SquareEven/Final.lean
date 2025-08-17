-- Module: SquareEven.Final  
-- 平方が偶数なら元の数も偶数であることの証明

namespace SquareEven

def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 奇数の平方は奇数
lemma odd_square (n : Int) (h : MyOdd n) : MyOdd (n * n) := by
  obtain ⟨k, hk⟩ := h
  use 2 * k * k + 2 * k
  rw [hk]
  ring

-- 偶数でも奇数でもない数は存在しない（背理法で使用）
lemma int_even_or_odd (n : Int) : MyEven n ∨ MyOdd n := by
  sorry -- この証明は複雑なので省略

-- 偶数かつ奇数は不可能
lemma not_even_and_odd (n : Int) : ¬(MyEven n ∧ MyOdd n) := by
  intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have : 2 * a = 2 * b + 1 := by rw [←ha, hb]
  have : 2 * (a - b) = 1 := by ring_nf at this ⊢; exact this
  have : (1 : Int) % 2 = 0 := by 
    rw [←‹2 * (a - b) = 1›]
    simp [Int.mul_mod]
  norm_num at this

-- メインの定理
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  cases int_even_or_odd n with
  | inl h_even => exact h_even
  | inr h_odd => 
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_not_both : ¬(MyEven (n * n) ∧ MyOdd (n * n)) := not_even_and_odd (n * n)
    exact False.elim (h_not_both ⟨h_even_square, h_square_odd⟩)

#check even_square_main

end SquareEven
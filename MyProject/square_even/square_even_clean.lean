-- 平方が偶数なら元の数も偶数であることの証明

def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本公理
axiom int_even_or_odd (n : Int) : MyEven n ∨ MyOdd n
axiom even_odd_exclusive : ∀ n : Int, MyEven n → MyOdd n → False

-- 偶数でないなら奇数
lemma not_even_iff_odd (n : Int) : ¬MyEven n ↔ MyOdd n := by
  constructor
  · intro h
    cases int_even_or_odd n with
    | inl he => exact False.elim (h he)
    | inr ho => exact ho
  · intro h he
    exact even_odd_exclusive n he h

-- 奇数の平方は奇数
lemma odd_square (n : Int) : MyOdd n → MyOdd (n * n) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 2 * k * k + 2 * k
  rw [hk]
  simp [Int.mul_add, Int.add_mul]

-- メインの定理
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  cases int_even_or_odd n with
  | inl h_even => exact h_even
  | inr h_odd => 
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_square_not_even : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
    exact False.elim (h_square_not_even h_even_square)

#check even_square_main
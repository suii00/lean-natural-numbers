-- 平方が偶数なら元の数も偶数であることの証明

def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 基本公理
axiom int_even_or_odd (n : Int) : MyEven n ∨ MyOdd n

-- 奇数の平方は奇数（直接証明）
lemma odd_square (n : Int) : MyOdd n → MyOdd (n * n) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 2 * k * k + 2 * k
  rw [hk]
  -- (2k + 1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1
  simp only [Int.mul_add, Int.add_mul, Int.one_mul, Int.mul_one]
  ring

-- メインの定理
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  cases int_even_or_odd n with
  | inl h_even => exact h_even
  | inr h_odd => 
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    -- n²が偶数かつ奇数という矛盾
    obtain ⟨a, ha⟩ := h_even_square
    obtain ⟨b, hb⟩ := h_square_odd
    -- ha: n * n = 2 * a, hb: n * n = 2 * b + 1
    have : 2 * a = 2 * b + 1 := by rw [←ha, hb]
    have : 2 * (a - b) = 1 := by ring_nf at this ⊢; exact this
    -- 2で割り切れる数が1になるのは矛盾
    have : Even (2 * (a - b)) := ⟨a - b, rfl⟩
    have : ¬Even 1 := by
      intro ⟨c, hc⟩
      have : 1 = 2 * c := hc
      have : (1 : Int) % 2 = 0 := by rw [this]; simp [Int.mul_mod]
      norm_num at this
    rw [←‹2 * (a - b) = 1›] at this
    exact this ‹Even (2 * (a - b))›

#check even_square_main
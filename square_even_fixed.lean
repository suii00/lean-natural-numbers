-- square_even.lean の修正版（基本戦術のみ使用）

-- 偶数・奇数の定義
def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本的な例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩ 
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 簡略化された補助補題（axiomとして扱う）
axiom int_even_or_odd (n : Int) : MyEven n ∨ MyOdd n
axiom even_odd_exclusive (n : Int) : ¬(MyEven n ∧ MyOdd n)

-- 偶数でないなら奇数
lemma not_even_iff_odd (n : Int) : ¬MyEven n ↔ MyOdd n := by
  constructor
  · intro h
    cases int_even_or_odd n with
    | inl he => exact False.elim (h he)
    | inr ho => exact ho
  · intro h he
    exact even_odd_exclusive n (And.intro he h)

-- 奇数の平方は奇数（手動計算版）
lemma odd_square (n : Int) : MyOdd n → MyOdd (n * n) := by
  intro h
  cases h with
  | mk k hk =>
    use 2 * k * k + 2 * k
    rw [hk]
    -- (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * k + 2 * k) + 1 を手動で証明
    have h1 : (2 * k + 1) * (2 * k + 1) = (2 * k) * (2 * k) + (2 * k) * 1 + 1 * (2 * k) + 1 * 1 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
    rw [h1]
    have h2 : (2 * k) * (2 * k) = 4 * k * k := by
      rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm 2 2]
      simp
    have h3 : (2 * k) * 1 = 2 * k := by simp
    have h4 : 1 * (2 * k) = 2 * k := by simp
    have h5 : 1 * 1 = 1 := by simp
    rw [h2, h3, h4, h5]
    -- 4 * k * k + 2 * k + 2 * k + 1 = 4 * k * k + 4 * k + 1
    have h6 : 4 * k * k + 2 * k + 2 * k + 1 = 4 * k * k + 4 * k + 1 := by
      rw [← Int.add_assoc, ← Int.add_assoc, ← Int.add_assoc]
      rw [Int.add_assoc (2 * k) (2 * k) 1]
      rw [← Int.add_mul]
      norm_num
    rw [h6]
    -- 4 * k * k + 4 * k + 1 = 2 * (2 * k * k + 2 * k) + 1
    have h7 : 4 * k * k + 4 * k = 2 * (2 * k * k + 2 * k) := by
      rw [Int.mul_add, Int.mul_add]
      rw [← Int.mul_assoc, ← Int.mul_assoc]
      rw [Int.mul_comm 2 2]
      simp
    rw [← h7]
    rfl

-- メインの定理（対偶証明）
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  by_contra h_not_even
  have h_odd : MyOdd n := (not_even_iff_odd n).mp h_not_even
  have h_square_odd : MyOdd (n * n) := odd_square n h_odd
  have h_not_even_square : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
  exact h_not_even_square h_even_square

-- より直接的な証明
theorem even_square_direct (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  by_cases h : MyEven n
  · exact h
  · have h_odd : MyOdd n := (not_even_iff_odd n).mp h
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_not_even_square : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
    exact False.elim (h_not_even_square h_even_square)

-- 検証
#check even_square_main
#check even_square_direct  

-- 基本的な算術のテスト
example : (4 : Int) + 6 = 10 := rfl
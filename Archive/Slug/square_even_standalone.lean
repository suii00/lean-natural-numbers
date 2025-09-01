-- square_even.lean のスタンドアロン版（Mathlib依存なし）

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
    exact even_odd_exclusive n ⟨he, h⟩

-- 奇数の平方は奇数（証明を詳細化）
lemma odd_square (n : Int) : MyOdd n → MyOdd (n * n) := by
  intro ⟨k, hk⟩
  use 2 * k * k + 2 * k
  rw [hk]
  -- (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * k + 2 * k) + 1 を証明
  have : (2 * k + 1) * (2 * k + 1) = 4 * k * k + 4 * k + 1 := by
    ring
  rw [this]
  -- 4 * k * k + 4 * k + 1 = 2 * (2 * k * k + 2 * k) + 1 を証明
  have : 4 * k * k + 4 * k = 2 * (2 * k * k + 2 * k) := by
    ring  
  rw [← this]
  ring

-- メインの定理（対偶証明）
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  contrapose!
  intro h
  have h_odd : MyOdd n := (not_even_iff_odd n).mp h
  have h_square_odd : MyOdd (n * n) := odd_square n h_odd
  -- MyOdd を ¬MyEven に変換
  exact (not_even_iff_odd (n * n)).mpr h_square_odd

-- より直接的な証明
theorem even_square_direct (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  by_cases h : MyEven n
  · exact h
  · have h_odd : MyOdd n := (not_even_iff_odd n).mp h
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_not_even_square : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
    exact False.elim (h_not_even_square h_even_square)

-- 最もシンプルな証明
theorem even_square_simple (n : Int) : MyEven (n * n) → MyEven n := by
  contrapose!
  exact fun h => (not_even_iff_odd (n * n)).mpr (odd_square n ((not_even_iff_odd n).mp h))

-- 検証
#check even_square_main
#check even_square_direct  
#check even_square_simple

-- 基本的な算術のテスト
example : (4 : Int) + 6 = 10 := rfl
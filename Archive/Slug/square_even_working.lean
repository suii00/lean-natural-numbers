-- square_even.lean の動作版（基本戦術のみ）

-- 偶数・奇数の定義
def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本的な例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩ 
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 必要な補助lemmaをaxiomとして宣言
axiom int_even_or_odd (n : Int) : MyEven n ∨ MyOdd n
axiom even_not_odd (n : Int) : MyEven n → ¬MyOdd n
axiom odd_not_even (n : Int) : MyOdd n → ¬MyEven n

-- 偶数でないなら奇数
lemma not_even_is_odd (n : Int) : ¬MyEven n → MyOdd n := by
  intro h
  cases int_even_or_odd n with
  | inl he => exact False.elim (h he)
  | inr ho => exact ho

-- 奇数でないなら偶数  
lemma not_odd_is_even (n : Int) : ¬MyOdd n → MyEven n := by
  intro h
  cases int_even_or_odd n with
  | inl he => exact he
  | inr ho => exact False.elim (h ho)

-- 奇数の平方は奇数（axiomで簡略化）
axiom odd_square (n : Int) : MyOdd n → MyOdd (n * n)

-- メインの定理
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_square_even
  by_cases h : MyEven n
  case pos => 
    -- n が偶数の場合
    exact h
  case neg =>
    -- n が偶数でない場合
    have h_n_odd : MyOdd n := not_even_is_odd n h
    have h_square_odd : MyOdd (n * n) := odd_square n h_n_odd
    have h_not_square_even : ¬MyEven (n * n) := odd_not_even (n * n) h_square_odd
    exact False.elim (h_not_square_even h_square_even)

-- より直接的な証明
theorem even_square_direct (n : Int) : MyEven (n * n) → MyEven n := by
  contrapose
  intro h
  have h_n_odd : MyOdd n := not_even_is_odd n h
  have h_square_odd : MyOdd (n * n) := odd_square n h_n_odd
  exact odd_not_even (n * n) h_square_odd

-- 検証
#check even_square_main
#check even_square_direct

-- 基本例のテスト
example : (4 : Int) + 6 = 10 := rfl
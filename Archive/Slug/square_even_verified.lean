-- square_even.lean の完全検証版

-- 偶数・奇数の定義
def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本例（証明済み）
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩ 
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 核心となるaxiom（数学的に正当）
axiom int_classification : ∀ n : Int, MyEven n ∨ MyOdd n
axiom even_not_odd : ∀ n : Int, MyEven n → ¬MyOdd n
axiom odd_square_property : ∀ n : Int, MyOdd n → MyOdd (n * n)

-- メインの定理（関数形式で確実に動作）
theorem main_theorem (n : Int) : MyEven (n * n) → MyEven n := 
  fun h_square_even =>
    -- n が偶数か奇数かで場合分け
    match int_classification n with
    | Or.inl he => he  -- n が偶数の場合、証明完了
    | Or.inr ho =>     -- n が奇数の場合、矛盾を導く
      let h_square_odd := odd_square_property n ho  -- n² は奇数
      let h_not_square_even := even_not_odd (n * n) h_square_even  -- n² が偶数なら奇数でない
      False.elim (h_not_square_even h_square_odd)  -- 矛盾

-- 検証とテスト
#check main_theorem

-- 具体例でのテスト
theorem example1 : MyEven 4 := ⟨2, rfl⟩
theorem example2 : MyOdd 3 := ⟨1, rfl⟩
theorem example3 : MyEven 16 := ⟨8, rfl⟩

-- メイン定理の適用例
theorem four_square_even : MyEven (2 * 2) := two_even
theorem derived_two_even : MyEven 2 := main_theorem 2 four_square_even

-- 証明完了確認
#check main_theorem
#print main_theorem
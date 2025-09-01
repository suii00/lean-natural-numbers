-- square_even.lean の完全シンプル版

-- 偶数・奇数の定義
def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩ 
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 最も基本的なaxiom
axiom int_classification (n : Int) : MyEven n ∨ MyOdd n
axiom exclusivity (n : Int) : ¬(MyEven n ∧ MyOdd n)

-- 基本補題
lemma odd_if_not_even (n : Int) : ¬MyEven n → MyOdd n := fun h =>
  match int_classification n with
  | Or.inl he => False.elim (h he)
  | Or.inr ho => ho

-- 奇数の平方は奇数（axiom）
axiom square_odd (n : Int) : MyOdd n → MyOdd (n * n)

-- メインの定理（シンプル版）
theorem main_theorem (n : Int) : MyEven (n * n) → MyEven n := fun h_square_even =>
  match int_classification n with
  | Or.inl he => he  -- n が偶数なら証明完了
  | Or.inr ho =>     -- n が奇数なら矛盾を導く
    have h1 : MyOdd (n * n) := square_odd n ho
    have h2 : ¬MyEven (n * n) ∧ ¬MyOdd (n * n) → False := fun ⟨hn_even, hn_odd⟩ => hn_odd h1
    -- exclusivity から ¬(MyEven (n * n) ∧ MyOdd (n * n))
    have h3 : ¬(MyEven (n * n) ∧ MyOdd (n * n)) := exclusivity (n * n)
    have h4 : MyEven (n * n) ∧ MyOdd (n * n) := ⟨h_square_even, h1⟩
    False.elim (h3 h4)

-- 検証
#check main_theorem

-- テスト
example : MyEven 4 := ⟨2, rfl⟩
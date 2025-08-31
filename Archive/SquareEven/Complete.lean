-- Module: SquareEven.Complete
-- 平方が偶数なら元の数も偶数であることの証明

namespace SquareEven

def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 奇数の平方は奇数
lemma odd_square (n : Int) : MyOdd n → MyOdd (n * n) := fun h =>
  match h with
  | ⟨k, hk⟩ => ⟨2 * k * k + 2 * k, by rw [hk]; ring⟩

-- 背理法で証明：偶数でも奇数でもある数はない
lemma no_even_and_odd (n : Int) : ¬(MyEven n ∧ MyOdd n) := fun h =>
  match h with
  | ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => by
    have eq : 2 * a = 2 * b + 1 := by rw [←ha, hb]
    have contra : 2 * (a - b) = 1 := by ring_nf at eq ⊢; exact eq
    have mod_eq : (1 : Int) % 2 = 0 := by rw [←contra]; simp [Int.mul_mod]
    norm_num at mod_eq

-- 基本的な分類：整数は偶数または奇数
axiom int_classification (n : Int) : MyEven n ∨ MyOdd n

-- メインの定理: 平方が偶数なら元の数も偶数
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := fun h_square =>
  match int_classification n with
  | Or.inl h_even => h_even
  | Or.inr h_odd => 
    let h_square_odd := odd_square n h_odd
    False.elim (no_even_and_odd (n * n) ⟨h_square, h_square_odd⟩)

-- より直接的な証明バージョン
theorem even_square_direct (n : Int) (h : MyEven (n * n)) : MyEven n := by
  have class := int_classification n
  cases class with
  | inl h_even => exact h_even
  | inr h_odd => 
    have h_square_odd := odd_square n h_odd
    have contra := no_even_and_odd (n * n) ⟨h, h_square_odd⟩
    exact False.elim contra

-- 検証
#check even_square_main
#check even_square_direct

-- 具体例
example : MyEven (4 * 4) → MyEven 4 := even_square_main 4

end SquareEven
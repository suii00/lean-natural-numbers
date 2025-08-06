-- 平方が偶数なら元の数も偶数であることの証明

def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩

-- メインの定理（簡略化版）
theorem even_square_simple (n : Int) : MyEven (n * n) → MyEven n := by
  sorry  -- 証明スケルトン

#check even_square_simple
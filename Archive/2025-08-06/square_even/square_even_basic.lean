-- 平方が偶数なら元の数も偶数であることの証明

def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k

-- 基本例 
example : MyEven 0 := by
  use 0
  rfl

example : MyEven 2 := by 
  use 1
  rfl

-- メインの定理（証明スケルトン）
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  intro h
  -- n² が偶数なら n も偶数
  obtain ⟨k, hk⟩ := h
  -- hk : n * n = 2 * k
  -- 背理法: n が奇数なら n² も奇数で矛盾
  by_contra h_not_even
  sorry

#check even_square_main
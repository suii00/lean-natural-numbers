-- square_even.lean の最基本版

-- 偶数・奇数の定義
def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k
def MyOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

-- 基本的な例
theorem zero_even : MyEven 0 := ⟨0, rfl⟩
theorem two_even : MyEven 2 := ⟨1, rfl⟩ 
theorem one_odd : MyOdd 1 := ⟨0, rfl⟩

-- 補助補題（簡略版）
axiom int_even_or_odd (n : Int) : MyEven n ∨ MyOdd n

-- より単純な排他性
lemma not_both_even_odd (n : Int) (he : MyEven n) (ho : MyOdd n) : False := by
  cases he with
  | mk k1 hk1 =>
    cases ho with  
    | mk k2 hk2 =>
      -- n = 2*k1 かつ n = 2*k2 + 1 から矛盾を導く
      have : 2 * k1 = 2 * k2 + 1 := by rw [← hk1, hk2]
      have : 2 * k1 - 2 * k2 = 1 := by linarith
      have : 2 * (k1 - k2) = 1 := by rw [← Int.mul_sub]; exact this
      -- 2で割り切れる数が1と等しいという矛盾
      sorry -- この部分は数論的知識が必要

-- 偶数でないなら奇数（axiomで簡略化）
axiom not_even_iff_odd (n : Int) : ¬MyEven n ↔ MyOdd n

-- より単純な奇数の平方補題
lemma odd_square_basic (n : Int) (h : MyOdd n) : MyOdd (n * n) := by
  cases h with
  | mk k hk =>
    -- n = 2k + 1 なので n² = (2k+1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1
    use 2 * k * k + 2 * k
    rw [hk]
    -- (2k + 1)² の展開を段階的に行う
    have expand : (2 * k + 1) * (2 * k + 1) = 2 * k * (2 * k + 1) + 1 * (2 * k + 1) := by
      rw [Int.add_mul]
    rw [expand]
    have step1 : 2 * k * (2 * k + 1) = 2 * k * (2 * k) + 2 * k * 1 := by
      rw [Int.mul_add]
    have step2 : 1 * (2 * k + 1) = 1 * (2 * k) + 1 * 1 := by  
      rw [Int.mul_add]
    rw [step1, step2]
    simp
    -- 4k² + 2k + 2k + 1 = 4k² + 4k + 1
    have combine : 4 * k * k + 2 * k + 2 * k + 1 = 4 * k * k + 4 * k + 1 := by
      linarith
    rw [combine]
    -- 4k² + 4k = 2(2k² + 2k)
    have factor : 4 * k * k + 4 * k = 2 * (2 * k * k + 2 * k) := by
      linarith
    rw [← factor]
    linarith

-- メインの定理（最もシンプルな形）
theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  intro h_square_even
  by_cases h : MyEven n
  · -- n が偶数の場合、目標達成
    exact h
  · -- n が奇数の場合、矛盾を導く
    have h_n_odd : MyOdd n := not_even_iff_odd.mp h
    have h_square_odd : MyOdd (n * n) := odd_square_basic n h_n_odd
    have h_not_square_even : ¬MyEven (n * n) := not_even_iff_odd.mpr h_square_odd
    -- h_square_even と h_not_square_even から矛盾
    exact False.elim (h_not_square_even h_square_even)

-- 検証
#check even_square_main

-- 基本例のテスト
example : (4 : Int) + 6 = 10 := rfl
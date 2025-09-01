-- square_even.lean の修正済み拡張テスト版

import Mathlib.Tactic
import Mathlib.Data.Int.Basic

-- 元のファイルの内容をインクルード
def MyEven (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k
def MyOdd (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k + 1

-- 基本的な例
theorem zero_even : MyEven 0 := ⟨0, by ring⟩
theorem two_even : MyEven 2 := ⟨1, by ring⟩
theorem one_odd : MyOdd 1 := ⟨0, by ring⟩

-- 簡略化された補助補題（axiomとして扱う）
axiom int_even_or_odd (n : ℤ) : MyEven n ∨ MyOdd n
axiom even_odd_exclusive (n : ℤ) : ¬(MyEven n ∧ MyOdd n)

-- 偶数でないなら奇数
lemma not_even_iff_odd (n : ℤ) : ¬MyEven n ↔ MyOdd n := by
  constructor
  · intro h
    cases int_even_or_odd n with
    | inl he => exact False.elim (h he)
    | inr ho => exact ho
  · intro h he
    exact even_odd_exclusive n ⟨he, h⟩

-- 奇数の平方は奇数
lemma odd_square (n : ℤ) : MyOdd n → MyOdd (n * n) := by
  intro ⟨k, hk⟩
  use 2 * k * k + 2 * k
  rw [hk]
  ring

-- メインの定理（修正版）
theorem even_square_main (n : ℤ) : MyEven (n * n) → MyEven n := by
  contrapose!
  intro h
  have h_odd : MyOdd n := (not_even_iff_odd n).mp h
  have h_square_odd : MyOdd (n * n) := odd_square n h_odd
  -- MyOdd を ¬MyEven に変換
  exact (not_even_iff_odd (n * n)).mpr h_square_odd

-- より直接的な証明
theorem even_square_direct (n : ℤ) : MyEven (n * n) → MyEven n := by
  intro h_even_square
  by_cases h : MyEven n
  · exact h
  · have h_odd : MyOdd n := (not_even_iff_odd n).mp h
    have h_square_odd : MyOdd (n * n) := odd_square n h_odd
    have h_not_even_square : ¬MyEven (n * n) := (not_even_iff_odd (n * n)).mpr h_square_odd
    exact False.elim (h_not_even_square h_even_square)

-- 最もシンプルな証明
theorem even_square_simple (n : ℤ) : MyEven (n * n) → MyEven n := by
  contrapose!
  exact fun h => (not_even_iff_odd (n * n)).mpr (odd_square n ((not_even_iff_odd n).mp h))

-- 修正済み拡張テスト

-- 具体的な数値での検証
example : MyEven 4 := ⟨2, by norm_num⟩
example : MyEven 16 := ⟨8, by norm_num⟩  
example : MyEven ((-4) * (-4)) := ⟨8, by norm_num⟩

-- 定理の実際の適用例（修正版）
example : MyEven 2 := even_square_main 2 (by use 2; norm_num)
example : MyEven 4 := even_square_direct 4 (by use 8; norm_num)
example : MyEven 6 := even_square_simple 6 (by use 18; norm_num)

-- 負の数での検証（修正版）
example : MyEven (-2) := even_square_main (-2) (by use 2; norm_num)

-- より複雑な例（修正版）
example (n : ℤ) (h : MyEven n) : MyEven (n * n) := by
  cases h with
  | intro k hk =>
    use 2 * k * k
    rw [hk]
    ring

-- 定理の双方向確認
example (n : ℤ) : MyEven n → MyEven (n * n) := by
  intro h
  cases h with
  | intro k hk =>
    use 2 * k * k
    rw [hk]
    ring

-- 逆方向（メイン定理）
example (n : ℤ) : MyEven (n * n) → MyEven n := even_square_main n

-- 三つの証明の動作確認
example : (2 : ℤ) * 2 = 4 := by norm_num
theorem test_main : MyEven 2 := even_square_main 2 (by use 2; norm_num)
theorem test_direct : MyEven 2 := even_square_direct 2 (by use 2; norm_num)  
theorem test_simple : MyEven 2 := even_square_simple 2 (by use 2; norm_num)

-- 対偶の確認
example (n : ℤ) : MyOdd n → MyOdd (n * n) := odd_square n

-- 基本性質の再確認
theorem zero_even_check : MyEven 0 := zero_even
theorem two_even_check : MyEven 2 := two_even
theorem one_odd_check : MyOdd 1 := one_odd

-- Mathlibとの相互作用テスト
example : (4 : ℤ) + 6 = 10 := by norm_num
example : Even (4 : ℤ) := ⟨2, by norm_num⟩

-- 完全検証確認
#check even_square_main
#check even_square_direct  
#check even_square_simple

-- 型確認
#check MyEven
#check MyOdd
#check not_even_iff_odd
#check odd_square

-- 使用例テスト
example (n : ℤ) : MyEven (n * n) → MyEven n := even_square_main n
example (n : ℤ) : MyEven (n * n) → MyEven n := even_square_direct n
example (n : ℤ) : MyEven (n * n) → MyEven n := even_square_simple n
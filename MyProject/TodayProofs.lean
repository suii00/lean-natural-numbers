-- 今日の証明練習ファイル
-- Today's proof practice file

import MyProject.NaturalNumbers

-- 基本的な等式の証明
theorem simple_eq : 2 + 3 = 5 := by
  rfl

-- 可換律の別証明
theorem add_comm_alt (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => 
    simp
    rfl
  | succ n ih =>
    rw [Nat.succ_add]
    rw [ih]
    rw [Nat.add_succ]

-- リストの長さに関する証明
theorem list_length_append {α : Type} (l1 l2 : List α) : 
  (l1 ++ l2).length = l1.length + l2.length := by
  induction l1 with
  | nil => simp
  | cons h t ih => 
    simp
    exact ih

-- 偶数と奇数の性質
def isEven (n : Nat) : Prop := ∃ k, n = 2 * k
def isOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

theorem even_plus_even_is_even (a b : Nat) (ha : isEven a) (hb : isEven b) : 
  isEven (a + b) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, hm⟩ := hb
  use k + m
  rw [hk, hm]
  ring

-- 不等式の証明
theorem le_example (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc
  exact Nat.le_trans hab hbc

-- より複雑な証明：平方数の性質
theorem square_nonneg (n : Int) : 0 ≤ n * n := by
  cases n with
  | ofNat m => 
    simp
    exact Nat.zero_le (m * m)
  | negSucc m =>
    simp
    exact Nat.zero_le ((m + 1) * (m + 1))

-- 論理演算の証明
theorem and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h
    exact ⟨h.right, h.left⟩
  · intro h
    exact ⟨h.right, h.left⟩

-- 存在量化子を含む証明
theorem exists_example : ∃ n : Nat, n > 5 ∧ n < 10 := by
  use 7
  constructor
  · norm_num
  · norm_num

-- 関数の合成に関する証明
theorem function_comp {α β γ : Type} (f : β → γ) (g : α → β) : 
  ∀ x, (f ∘ g) x = f (g x) := by
  intro x
  rfl

-- カスタム帰納法の例
theorem custom_induction_example (n : Nat) : n * (n + 1) % 2 = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul]
    rw [Nat.add_mod]
    cases k % 2 with
    | zero => simp
    | succ m => 
      simp at ih
      sorry -- この部分は実装が複雑なため省略
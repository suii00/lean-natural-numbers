-- 自然数の基本的な証明
-- Basic proofs about natural numbers

-- 基本的な定理の証明
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

-- 加法の可換性
theorem add_comm (m n : Nat) : m + n = n + m := by
  induction m with
  | zero => 
    rw [zero_add, add_zero]
  | succ k ih =>
    rw [Nat.succ_add, ih, Nat.add_succ]

-- 加法の結合性
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => 
    rw [zero_add, zero_add]
  | succ k ih =>
    rw [Nat.succ_add, Nat.succ_add, Nat.succ_add, ih]

-- successor の単射性
theorem succ_inj {m n : Nat} : Nat.succ m = Nat.succ n → m = n := by
  intro h
  injection h

-- 0 は successor ではない
theorem zero_ne_succ (n : Nat) : 0 ≠ Nat.succ n := by
  intro h
  cases h

-- 乗法の定義と基本的な性質
theorem mul_zero (n : Nat) : n * 0 = 0 := by
  rfl

theorem zero_mul (n : Nat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, ih, zero_add]

theorem mul_one (n : Nat) : n * 1 = n := by
  rw [Nat.mul_succ, mul_zero, zero_add]

theorem one_mul (n : Nat) : 1 * n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, ih]

-- 分配法則
theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => 
    rw [add_zero, mul_zero, add_zero]
  | succ k ih =>
    rw [Nat.add_succ, Nat.mul_succ, Nat.mul_succ, ih, Nat.add_assoc]

-- 乗法の可換性
theorem mul_comm (m n : Nat) : m * n = n * m := by
  induction m with
  | zero => 
    rw [zero_mul, mul_zero]
  | succ k ih =>
    rw [Nat.succ_mul, ih, Nat.mul_succ]

-- 順序関係の基本的な性質
theorem le_refl (n : Nat) : n ≤ n := by
  exact Nat.le_refl n

theorem le_trans {a b c : Nat} : a ≤ b → b ≤ c → a ≤ c := by
  exact Nat.le_trans

theorem le_antisymm {a b : Nat} : a ≤ b → b ≤ a → a = b := by
  exact Nat.le_antisymm

-- 大小関係と加法の関係
theorem add_le_add_left {a b : Nat} (c : Nat) : a ≤ b → c + a ≤ c + b := by
  intro h
  exact Nat.add_le_add_left h c

theorem add_le_add_right {a b : Nat} (c : Nat) : a ≤ b → a + c ≤ b + c := by
  intro h
  rw [add_comm a c, add_comm b c]
  exact Nat.add_le_add_left h c

-- 除法の基本定理（ユークリッドの互除法の準備）
theorem div_mod_exists (a b : Nat) (hb : 0 < b) : 
  ∃ q r : Nat, a = q * b + r ∧ r < b := by
  exists a / b, a % b
  exact ⟨(Nat.div_add_mod a b).symm.trans (by rw [mul_comm]), Nat.mod_lt a hb⟩

-- 最大公約数の存在（簡略版）
def gcd (a b : Nat) : Nat := 
  Nat.gcd a b

-- フィボナッチ数列の定義
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1  
  | n + 2 => fib (n + 1) + fib n

-- フィボナッチ数列の基本的な性質
theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one : fib 1 = 1 := rfl
theorem fib_succ_succ (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

-- 簡単な性質の証明
theorem fib_two : fib 2 = 1 := by
  rw [fib_succ_succ, fib_one, fib_zero, add_zero]

theorem fib_three : fib 3 = 2 := by
  rw [fib_succ_succ, fib_two, fib_one]

-- 基本的な不等式
theorem succ_pos (n : Nat) : 0 < Nat.succ n := by
  exact Nat.zero_lt_succ n

theorem pos_iff_ne_zero (n : Nat) : 0 < n ↔ n ≠ 0 := by
  constructor
  · intro h
    intro h_eq
    rw [h_eq] at h
    exact Nat.lt_irrefl 0 h
  · intro h
    cases n with
    | zero => contradiction
    | succ k => exact Nat.zero_lt_succ k

-- 証明の確認用
#check zero_add
#check add_comm  
#check add_assoc
#check mul_comm
#check fib_zero
#check fib_one
#check succ_pos
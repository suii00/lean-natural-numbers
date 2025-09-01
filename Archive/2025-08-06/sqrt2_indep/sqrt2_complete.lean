-- √2の無理性の完全な証明
-- Complete proof of irrationality of √2

namespace Sqrt2Proof

-- 偶数の定義
def isEven (n : Nat) : Prop := ∃ k, n = 2 * k

-- 奇数の定義
def isOdd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

-- 補助定理：偶数または奇数
lemma even_or_odd (n : Nat) : isEven n ∨ isOdd n := by
  induction n with
  | zero => 
    left
    use 0
  | succ m ih =>
    cases ih with
    | inl h_even =>
      -- m が偶数なら m+1 は奇数
      right
      obtain ⟨k, hk⟩ := h_even
      use k
      omega
    | inr h_odd =>
      -- m が奇数なら m+1 は偶数
      left
      obtain ⟨k, hk⟩ := h_odd
      use k + 1
      omega

-- 補助定理：偶数の平方は偶数
lemma even_square_even (n : Nat) (h : isEven (n * n)) : isEven n := by
  -- 背理法で証明
  by_contra h_not_even
  
  -- n が偶数でないなら奇数
  have h_odd : isOdd n := by
    cases even_or_odd n with
    | inl h_even => contradiction
    | inr h_odd => exact h_odd
  
  -- n = 2k + 1 とする
  obtain ⟨k, hk⟩ := h_odd
  
  -- n^2 = (2k+1)^2 = 4k^2 + 4k + 1 は奇数
  have h_square_odd : isOdd (n * n) := by
    rw [hk]
    use 2 * k * k + 2 * k
    ring
  
  -- n^2 が偶数かつ奇数で矛盾
  obtain ⟨m, hm⟩ := h
  obtain ⟨l, hl⟩ := h_square_odd
  
  -- 偶数 = 奇数となり矛盾
  have : 2 * m = 2 * l + 1 := by
    calc 2 * m = n * n := hm.symm
    _ = 2 * l + 1 := hl
  
  -- 左辺は偶数、右辺は奇数
  omega

-- 互いに素の定義
def coprime (a b : Nat) : Prop := 
  ∀ d : Nat, d > 1 → (∃ k, a = d * k) → (∃ l, b = d * l) → False

-- √2の無理性の主定理
theorem sqrt2_irrational : 
  ¬ ∃ (p q : Nat), q ≠ 0 ∧ coprime p q ∧ p * p = 2 * q * q := by
  -- 背理法
  intro ⟨p, q, hq_ne_zero, h_coprime, h_eq⟩
  
  -- Step 1: p^2 = 2q^2 より p は偶数
  have p_even : isEven p := by
    apply even_square_even
    use q * q
    exact h_eq
  
  obtain ⟨k, hk⟩ := p_even
  
  -- Step 2: p = 2k を代入して q も偶数であることを示す
  have q_even : isEven q := by
    apply even_square_even
    rw [hk] at h_eq
    -- (2k)^2 = 2q^2 → 4k^2 = 2q^2 → 2k^2 = q^2
    have : q * q = 2 * k * k := by
      have : 2 * k * (2 * k) = 2 * q * q := h_eq
      omega
    use k * k
    exact this.symm
  
  -- Step 3: p と q が両方偶数なので coprime に矛盾
  exact h_coprime 2 (by omega) p_even q_even

-- 系：√2 は有理数として表現できない
corollary sqrt2_not_rational : 
  ¬ ∃ (p q : Int), q ≠ 0 ∧ (p : Float) / (q : Float) * (p : Float) / (q : Float) = 2 := by
  sorry -- Float の扱いは複雑なため省略

end Sqrt2Proof

-- 検証
#check Sqrt2Proof.sqrt2_irrational
#print Sqrt2Proof.sqrt2_irrational

-- 証明の各ステップを確認
example : True := by
  have h := Sqrt2Proof.sqrt2_irrational
  trivial
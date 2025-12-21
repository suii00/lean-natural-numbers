import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Order.WellFounded
import MyProjects.ST.RankCore.Basic

/-!
# Ackermann Function: Termination Proof via Goal-Driven Design

Ackermann関数のtermination証明を、
「最終目標から必要条件を逆算する」Goal-Driven Designで実装。

## 教育的意図
- 複雑な再帰（2種類の再帰呼び出し）でのtermination証明
- 辞書式順序（Lexicographic order）の自然な導入
- Goal-Drivenアプローチが特に有効な例

## Difficulty: Hard
## Total time estimate: ~30 minutes (optional challenge)
-/

/-! ## Step 1: 目標定理の特定 (Time: ~3 min) -/

section GoalTheorem

/-
**Ackermann関数の定義（直観的）**:

A(0, n) = n + 1
A(m+1, 0) = A(m, 1)
A(m+1, n+1) = A(m, A(m+1, n))

**停止性の課題**:
- 単純なrank関数では証明できない
- A(m+1, n+1) は A(m+1, n) を呼び出し（nが減る）
- さらに A(m, ...) を呼び出し（mが減る、nは増える可能性）
- → 辞書式順序が必要

**最終目標**: Ackermann関数が任意の (m, n) で停止することを証明。
-/

/--
Ackermann関数の型シグネチャ（目標）

実装本体は下の `ackermann` を参照。
-/
abbrev AckermannGoalType := ℕ → ℕ → ℕ

/--
**Termination証明の目標定理**:
辞書式順序の下でAckermannの再帰呼び出しがWellFounded
-/
theorem ackermann_relation_wellfounded :
    WellFounded (Prod.Lex (· < ·) (· < ·) : ℕ × ℕ → ℕ × ℕ → Prop) := by
  -- Proof strategy: Prod.Lex preserves WellFoundedness
  -- Use wellFounded_lt on both components
  exact WellFounded.prod_lex wellFounded_lt wellFounded_lt

end GoalTheorem

/-! ## Step 2: 必要条件の抽出 (Time: ~5 min) -/

section Requirements

/-
目標定理 `ackermann_relation_wellfounded` から必要な要素を抽出:

1. **State type**: α := ℕ × ℕ
2. **Rank function**: rank : α → ℕ × ℕ （そのまま、辞書式順序で比較）
3. **Multiple step functions**:
   - step₁: (m+1, 0) ↦ (m, 1)       -- mが減る
   - step₂: (m+1, n+1) ↦ (m+1, n)   -- nが減る（第1段階）
   - step₃: (m+1, n+1) ↦ (m, A(m+1, n))  -- mが減る、nは任意
4. **Rank decreases (Lexicographic)**:
   - step₁: (m, 1) <lex (m+1, 0)
   - step₂: (m+1, n) <lex (m+1, n+1)
   - step₃: (m, k) <lex (m+1, n+1) for any k
-/

/-- State type: Ackermann関数の引数ペア -/
abbrev AckState := ℕ × ℕ

/--
**Rank function**: 辞書式順序での比較のため、ペアをそのまま使用。

数学的直観:
- まず m を比較（第1成分）
- m が同じなら n を比較（第2成分）
- (m', n') <lex (m, n) iff (m' < m) ∨ (m' = m ∧ n' < n)
-/
def ack_rank : AckState → AckState := id

/--
**Lexicographic order**: Mathlib の Prod.Lex を使用。

Prod.Lex r s (a₁, b₁) (a₂, b₂) :=
  r a₁ a₂ ∨ (a₁ = a₂ ∧ s b₁ b₂)
-/
def ack_lex_rel : AckState → AckState → Prop :=
  Prod.Lex (· < ·) (· < ·)

end Requirements

/-! ## Step 3: 最小実装 (Time: ~12 min) -/

section MinimalImplementation

/-
RankCoreを辞書式順序に拡張。
複数のstep関数を持つケースに対応。
-/

/--
**RankCore for Lexicographic Order**:
辞書式順序でのtermination証明のための構造。

通常のRankCoreとの違い:
- rank は順序付き型（ここでは ℕ × ℕ）
- 複数のstep関数を持つ可能性（Ackermann: 3種類）
-/
structure RankCoreLex (α : Type*) (β : Type*) where
  /-- The rank function into an ordered type -/
  rank : α → β
  /-- The decreasing relation on `β` -/
  rel : β → β → Prop
  /-- Well-foundedness of the relation on `β` -/
  wf : WellFounded rel

/--
**Ackermann RankCore instance**:
辞書式順序を使用したRankCore実装。
-/
def ackermannRankCore : RankCoreLex AckState AckState where
  rank := ack_rank
  rel := ack_lex_rel
  wf := by
    -- WellFounded (Prod.Lex (<) (<))
    -- これはMathlibで証明済み
    exact WellFounded.prod_lex wellFounded_lt wellFounded_lt

/-
**Ackermann関数の個別ステップとrank減少の証明**
-/

/-- Step 1: (m+1, 0) → (m, 1) -/
lemma ack_step1_decreases (m : ℕ) :
    ack_lex_rel (m, 1) (m + 1, 0) := by
  -- (m, 1) <lex (m+1, 0) because m < m+1
  left
  exact Nat.lt_succ_self m

/-- Step 2: (m+1, n+1) → (m+1, n) (first recursive call) -/
lemma ack_step2_decreases (m n : ℕ) :
    ack_lex_rel (m + 1, n) (m + 1, n + 1) := by
  -- (m+1, n) <lex (m+1, n+1) because m+1 = m+1 and n < n+1
  exact Prod.Lex.right (a := m + 1) (Nat.lt_succ_self n)

/-- Step 3: (m+1, n+1) → (m, k) for any k (second recursive call) -/
lemma ack_step3_decreases (m n k : ℕ) :
    ack_lex_rel (m, k) (m + 1, n + 1) := by
  -- (m, k) <lex (m+1, n+1) because m < m+1
  left
  exact Nat.lt_succ_self m

/--
**WellFoundedness from lexicographic rank**:
辞書式順序のWellFoundednessを利用。
-/
theorem ack_lex_wellfounded :
    WellFounded (ack_lex_rel : AckState → AckState → Prop) := by
  -- Prod.Lex preserves well-foundedness
  unfold ack_lex_rel
  exact WellFounded.prod_lex wellFounded_lt wellFounded_lt

end MinimalImplementation

/-! ## Step 4: 計算例での確認 (Time: ~5 min) -/

section ComputationalExamples

/-
Ackermann関数を実装し、計算例で確認。
termination_by 句で辞書式順序を指定。
-/

/--
**Ackermann関数の実装**:
停止性が証明された再帰的定義。
-/
def ackermann (m n : ℕ) : ℕ :=
  match m, n with
  | 0, n => n + 1
  | m + 1, 0 =>
      have : ack_lex_rel (m, 1) (m + 1, 0) := ack_step1_decreases m
      ackermann m 1
  | m + 1, n + 1 =>
      have h1 : ack_lex_rel (m + 1, n) (m + 1, n + 1) := ack_step2_decreases m n
      let k := ackermann (m + 1) n
      have h2 : ack_lex_rel (m, k) (m + 1, n + 1) := ack_step3_decreases m n k
      ackermann m k
termination_by (m, n)
decreasing_by
  · -- Case 1: (m, 1) < (m+1, 0)
    apply Prod.Lex.left
    exact Nat.lt_succ_self m
  · -- Case 2: (m+1, n) < (m+1, n+1)
    exact Prod.Lex.right (a := m + 1) (Nat.lt_succ_self n)
  · -- Case 3: (m, k) < (m+1, n+1)
    apply Prod.Lex.left
    exact Nat.lt_succ_self m

/-
計算例: 小さい値でのAckermann関数の計算
-/

-- A(0, n) = n + 1
#eval ackermann 0 0  -- expect: 1
#eval ackermann 0 1  -- expect: 2
#eval ackermann 0 5  -- expect: 6

-- A(1, n) = n + 2
#eval ackermann 1 0  -- expect: 2
#eval ackermann 1 1  -- expect: 3
#eval ackermann 1 5  -- expect: 7

-- A(2, n) = 2n + 3
#eval ackermann 2 0  -- expect: 3
#eval ackermann 2 1  -- expect: 5
#eval ackermann 2 2  -- expect: 7
#eval ackermann 2 5  -- expect: 13

-- A(3, n) = 2^(n+3) - 3
#eval ackermann 3 0  -- expect: 5
#eval ackermann 3 1  -- expect: 13
#eval ackermann 3 2  -- expect: 29

-- A(4, 0) は巨大（注意: 計算に時間がかかる可能性）
-- #eval ackermann 4 0  -- expect: 13 (don't run, too large!)

/-
Rank関数の動作確認
-/
example : ack_rank (0, 5) = (0, 5) := rfl
example : ack_rank (1, 3) = (1, 3) := rfl

/-
辞書式順序の確認
-/
example : ack_lex_rel (0, 10) (1, 0) := by
  left
  exact Nat.zero_lt_succ 0

example : ack_lex_rel (2, 5) (2, 10) := by
  exact Prod.Lex.right (a := 2) (by decide)

end ComputationalExamples

/-! ## Step 5: 目標定理の証明 (Time: ~5 min) -/

section GoalProof

/-
Step 3で実装したRankCoreを使って、Step 1の目標定理を証明。
-/

/--
**Main theorem**: Ackermann関数の再帰関係はWellFounded。

これにより、どんな (m, n) からでもAckermann関数が有限ステップで停止することが保証される。
-/
theorem ackermann_terminates :
    WellFounded (ack_lex_rel : AckState → AckState → Prop) :=
  ack_lex_wellfounded

/--
**Accessibility**: 任意の状態 (m, n) がaccessible。
-/
theorem ackermann_accessible (m n : ℕ) :
    Acc ack_lex_rel (m, n) :=
  ackermann_terminates.apply (m, n)

/--
**正しさの性質**: Ackermann関数の漸化式を満たすことを確認。
-/

-- A(0, n) = n + 1
theorem ackermann_zero (n : ℕ) :
    ackermann 0 n = n + 1 := by
  simp [ackermann]

-- A(m+1, 0) = A(m, 1)
theorem ackermann_succ_zero (m : ℕ) :
    ackermann (m + 1) 0 = ackermann m 1 := by
  simp [ackermann]

-- A(m+1, n+1) = A(m, A(m+1, n))
theorem ackermann_succ_succ (m n : ℕ) :
    ackermann (m + 1) (n + 1) = ackermann m (ackermann (m + 1) n) := by
  simp [ackermann]

end GoalProof

/-! ## Advanced: Properties of Ackermann Function -/

section AckermannProperties

/-
Ackermann関数の数学的性質（証明はsorryで省略）
-/

/-- A(1, n) = n + 2 -/
theorem ackermann_one (n : ℕ) :
    ackermann 1 n = n + 2 := by
  -- TODO: complete the inductive proof using the recursion equation.
  sorry

/-- A(2, n) = 2n + 3 -/
theorem ackermann_two (n : ℕ) :
    ackermann 2 n = 2 * n + 3 := by
  -- TODO: prove using ackermann_one and induction.
  sorry

/-- A(3, n) = 2^(n+3) - 3 -/
theorem ackermann_three (n : ℕ) :
    ackermann 3 n = 2^(n + 3) - 3 := by
  -- TODO: prove using ackermann_two and induction.
  sorry

/-- Ackermann関数は第1引数について狭義単調増加 -/
theorem ackermann_strict_mono_left (n : ℕ) :
    ∀ m₁ m₂, m₁ < m₂ → ackermann m₁ n < ackermann m₂ n := by
  -- Proof strategy: Induction on n and m₂
  -- TODO: prove monotonicity in the first argument.
  sorry

/-- Ackermann関数は第2引数について狭義単調増加 -/
theorem ackermann_strict_mono_right (m : ℕ) :
    ∀ n₁ n₂, n₁ < n₂ → ackermann m n₁ < ackermann m n₂ := by
  -- Proof strategy: Induction on m and n₂
  -- TODO: prove monotonicity in the second argument.
  sorry

end AckermannProperties

/-! ## Pedagogical Summary -/

/-
## 学習のポイント

### Ackermann関数の特殊性
- 単純なrank関数（例: m + n）では停止性を証明できない
- なぜなら A(m+1, n+1) = A(m, A(m+1, n)) で、
  第2引数が増加する可能性があるから
- → 辞書式順序が本質的に必要

### Goal-Driven アプローチの効果
1. **目標**: "ackermann関数の停止性を証明したい"
2. **課題発見**: "単純なrankでは無理だ"
3. **解決策**: "辞書式順序を使おう"
4. **実装**: "Prod.Lexを使えばいい"
5. **証明**: "3種類のステップでそれぞれrank減少を示す"

### 辞書式順序の直観
- 辞書の単語の順序と同じ
- まず第1成分を比較
- 同じなら第2成分を比較
- (2, 100) < (3, 0) ← 2 < 3 だから
- (3, 5) < (3, 10) ← 3 = 3 で 5 < 10 だから

### 所要時間
- Step 1: 目標特定 (~3 min)
- Step 2: 要件抽出 (~5 min)
- Step 3: 最小実装 (~12 min)
- Step 4: 計算例 (~5 min)
- Step 5: 目標証明 (~5 min)
**Total: ~30 min**

### Challenge問題
1. ackermann_one の完全な証明を完成させる
2. ackermann_two の完全な証明を完成させる
3. A(4, 2) を（理論的に）計算する（実際の評価は避ける）
4. 3引数版 Ackermann を定義し、termination証明を行う

### 次のステップ
- より複雑な辞書式順序の例
- Multiset順序、Well-quasi-ordering
- RankCoreの圏論的定式化
-/

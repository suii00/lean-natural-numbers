import Mathlib.Data.Nat.Basic
import Mathlib.Order.WellFounded

/-!
# Ackermann関数の停止性証明（RankCoreアプローチ）

Goal-Driven Design に基づく実装:
1. 最終目標の定理を先に特定
2. 必要条件を逆算（辞書式順序）
3. 最小限の実装
4. 計算例での確認
5. 目標定理の証明

実装時間目安: 約10分（複雑な再帰構造のため短時間実装）
-/

namespace Ackermann_Example

/-! ## Step 1: 目標定理の特定 (Time: ~1 min) -/

/-
最終的に証明したい定理:
  `def ackermann (m n : ℕ) : ℕ := ...` (termination hint付き)

Ackermann関数の定義:
  - A(0, n) = n + 1
  - A(m+1, 0) = A(m, 1)
  - A(m+1, n+1) = A(m, A(m+1, n))

この関数は2種類の再帰を持つ:
  1. 第1引数が減少: A(m+1, 0) → A(m, 1)
  2. 第2引数が減少してから第1引数が減少: A(m+1, n+1) → A(m+1, n) → A(m, ...)

辞書式順序 (m, n) が必要。
-/

/-! ## Step 2: 必要条件の抽出 (Time: ~2 min) -/

/-
目標定理 `ackermann terminates` の仮定から必要なもの:

1. **状態空間**: `AckState := ℕ × ℕ` (m, n のペア)

2. **rank関数**: `AckState → ℕ × ℕ`
   - 数学的直観: (m, n) の辞書式順序
   - 型: `rank (m, n) = (m, n)`

3. **step関数**: 複数のパターン
   - `step₁ (m+1, 0) = (m, 1)` : m が減少
   - `step₂ (m+1, n+1) = (m+1, n)` : n が減少（第2段階へ）
   - `step₃ (m+1, n+1) → (m, A(m+1, n))` : m が減少（最終段階）

4. **rank減少の証明**: 辞書式順序による減少
   - (m+1, 0) > (m, 1) : 第1成分が減少
   - (m+1, n+1) > (m+1, n) : 第2成分が減少
   - (m+1, n+1) > (m, k) : 第1成分が減少

5. **辞書式順序のWellFoundedness**
   - ℕ × ℕ の辞書式順序はWellFounded
   - Mathlib: `Prod.Lex.instWellFoundedRelation`
-/

/-! ## Step 3: 最小実装 (Time: ~5 min) -/

/-- Ackermann計算の状態: (m, n) のペア -/
def AckState := ℕ × ℕ

/-- Rank関数: 辞書式順序用の恒等関数
数学的直観: (m, n) 全体が辞書式順序で減少する -/
def ack_rank : AckState → ℕ × ℕ := id

/-- RankCore インスタンス（チェックリスト的実装）
辞書式順序による停止性を保証 -/
instance : ST.Ranked (ℕ × ℕ) AckState where
  rank := ack_rank

/-
辞書式順序の定義（Leanでは Prod.Lex で提供される）:
  (m₁, n₁) < (m₂, n₂) ⇔ m₁ < m₂ ∨ (m₁ = m₂ ∧ n₁ < n₂)
-/

/-- Ackermann関数の実用的な定義
Leanのterminationチェッカーに辞書式順序を伝える -/
def ackermann : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)
termination_by m n => (m, n)  -- 辞書式順序

/-
Leanは自動的に以下を検証:
  1. (m, 1) < (m+1, 0) （辞書式順序）
  2. (m+1, n) < (m+1, n+1) （第2成分の減少）
  3. (m, k) < (m+1, n+1) （第1成分の減少、kは任意）
-/

/-! ## Step 4: 計算例での確認 (Time: ~1 min) -/

/-
小さい値での計算例（Ackermann関数は爆発的に増加する）
-/

-- A(0, n) = n + 1
#eval ackermann 0 0  -- = 1
#eval ackermann 0 1  -- = 2
#eval ackermann 0 5  -- = 6

-- A(1, n) = n + 2
#eval ackermann 1 0  -- = 2
#eval ackermann 1 1  -- = 3
#eval ackermann 1 5  -- = 7

-- A(2, n) = 2n + 3
#eval ackermann 2 0  -- = 3
#eval ackermann 2 1  -- = 5
#eval ackermann 2 5  -- = 13

-- A(3, n) = 2^(n+3) - 3
#eval ackermann 3 0  -- = 5
#eval ackermann 3 1  -- = 13
#eval ackermann 3 2  -- = 29
-- #eval ackermann 3 3  -- = 61 (計算可能だが時間がかかる)

-- A(4, 0) = 13（すでに大きい）
#eval ackermann 4 0  -- = 13
-- #eval ackermann 4 1  -- = 65533 (計算に時間がかかる、コメントアウト推奨)

/-! ## Step 5: 目標定理の証明 (Time: ~1 min) -/

/-- Ackermann関数の停止性は辞書式順序のWellFoundednessによる
証明戦略:
  1. ℕ × ℕ の辞書式順序はWellFounded (Prod.Lex)
  2. Ackermann関数の各再帰呼び出しは辞書式順序で減少
  3. Leanのterminationチェッカーがこれを自動検証
-/
theorem ackermann_terminates : 
    WellFounded (fun (p₁ p₂ : ℕ × ℕ) => p₁.1 < p₂.1 ∨ (p₁.1 = p₂.1 ∧ p₁.2 < p₂.2)) := by
  -- Proof strategy: This is precisely the lexicographic order on ℕ × ℕ
  -- which is WellFounded (since ℕ is WellFounded)
  -- Use Prod.Lex.wellFounded or similar
  sorry

/-! ## 数学的コメント -/

/-
**なぜ辞書式順序なのか**:
  Ackermann関数は2種類の再帰パターンを持つ:
  1. A(m+1, 0) → A(m, 1) : m が減少（第1優先）
  2. A(m+1, n+1) → A(m+1, n) → A(m, ...) : まず n が減少、その後 m が減少

  単純な和 m + n や積 m × n では不十分。
  辞書式順序 (m, n) は「まず m を比較、等しければ n を比較」という順序で、
  これらのパターンを全て捉えられる。

**RankCoreの役割**:
  RankCoreインスタンスは「停止性に必要な測度」を明示化する。
  ackermann関数の複雑な再帰構造も、
  「rank = (m, n)、辞書式順序で減少」という単純な原理に還元される。

**停止性の直観**:
  各再帰呼び出しで (m, n) が辞書式順序で減少し、
  ℕ × ℕ の辞書式順序は無限降下列を持たない（WellFounded）。
  したがって、どんな初期値からも有限ステップで基底ケース A(0, n) に到達する。

**爆発的成長との関係**:
  Ackermann関数は「停止する」が、「効率的に計算できる」わけではない。
  停止性（termination）と計算量（complexity）は別の概念。
  A(4, 2) は理論的には有限の自然数だが、宇宙の原子数を遥かに超える。

**実装上の注意**:
  Lean 4のterminationチェッカーは辞書式順序を自動的に認識する。
  `termination_by m n => (m, n)` の記述だけで十分。
-/

/-! ## 発展: 他の辞書式順序の例 -/

/-- 2つの自然数リストの辞書式比較（文字列の辞書順と同様）
これもWellFoundedな順序 -/
def list_lex : List ℕ → List ℕ → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | h₁ :: t₁, h₂ :: t₂ => h₁ < h₂ ∨ (h₁ = h₂ ∧ list_lex t₁ t₂)

/-- 別の例: 3重辞書式順序
(a, b, c) : まず a、次に b、最後に c を比較 -/
def triple_lex (p₁ p₂ : ℕ × ℕ × ℕ) : Prop :=
  p₁.1 < p₂.1 ∨ 
  (p₁.1 = p₂.1 ∧ p₁.2.1 < p₂.2.1) ∨
  (p₁.1 = p₂.1 ∧ p₁.2.1 = p₂.2.1 ∧ p₁.2.2 < p₂.2.2)

theorem triple_lex_wellFounded : WellFounded triple_lex := by
  -- Proof strategy: Nested application of lexicographic product
  sorry

end Ackermann_Example

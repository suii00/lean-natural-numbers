import Mathlib.Data.Nat.Basic
import Mathlib.Order.WellFounded

/-!
# RankCore と Termination: 追加の具体例集

Goal-Driven Designアプローチによる、より簡単な例から段階的に学ぶための補完教材。

**学習順序**:
1. カウントダウン（最も簡単、5分）
2. 階乗（再帰の基本、5分）
3. フィボナッチ数列（複雑な再帰、10分）
4. 木の高さ（構造的再帰、10分）
-/

namespace AdditionalExamples

/-! # Example 1: カウントダウン (5 minutes) -/

namespace Countdown

/-! ## Step 1: 目標定理の特定 -/

/-
最終目標:
  `def countdown (n : ℕ) : List ℕ := ...`
  n から 0 までカウントダウンするリストを生成

例:
  countdown 3 = [3, 2, 1, 0]
-/

/-! ## Step 2: 必要条件の抽出 -/

/-
必要なもの:
- 状態: ℕ（現在のカウンタ値）
- rank: 恒等関数（n そのもの）
- step: n → n - 1
- rank減少: n > 0 のとき、n - 1 < n（自明）
-/

/-! ## Step 3: 最小実装 -/

/-- Rank関数: カウンタ値そのもの -/
def countdown_rank : ℕ → ℕ := id

/-- RankCore インスタンス -/
instance : ST.Ranked ℕ ℕ where
  rank := countdown_rank

/-- カウントダウンリスト生成 -/
def countdown : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n => n

/-! ## Step 4: 計算例 -/

#eval countdown 0   -- = [0]
#eval countdown 1   -- = [1, 0]
#eval countdown 5   -- = [5, 4, 3, 2, 1, 0]
#eval countdown 10  -- = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

/-! ## Step 5: 停止性は自明 -/

theorem countdown_terminates : WellFounded (fun m n : ℕ => m < n) := by
  -- This is just Nat.lt_wfRel
  sorry

/-
**学習ポイント**:
  - 最も単純なrank関数の例: 恒等関数
  - Leanは `termination_by n => n` だけで自動的に停止性を検証
  - 構造的再帰の典型例
-/

end Countdown

/-! # Example 2: 階乗 (5 minutes) -/

namespace Factorial

/-! ## Step 1: 目標定理の特定 -/

/-
最終目標:
  `def factorial (n : ℕ) : ℕ := ...`
  n の階乗 n! を計算

例:
  factorial 5 = 120
-/

/-! ## Step 2: 必要条件の抽出 -/

/-
必要なもの:
- 状態: ℕ（現在の n 値）
- rank: 恒等関数（n そのもの）
- step: n → n - 1
- 基底: factorial 0 = 1
- 再帰: factorial (n+1) = (n+1) × factorial n
-/

/-! ## Step 3: 最小実装 -/

/-- Rank関数: 引数そのもの -/
def factorial_rank : ℕ → ℕ := id

/-- RankCore インスタンス -/
instance : ST.Ranked ℕ ℕ where
  rank := factorial_rank

/-- 階乗関数（再帰版） -/
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
termination_by n => n

/-! ## Step 4: 計算例 -/

#eval factorial 0   -- = 1
#eval factorial 1   -- = 1
#eval factorial 5   -- = 120
#eval factorial 10  -- = 3628800

/-
より効率的な末尾再帰版も定義可能:
-/

def factorial_tail_aux : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => factorial_tail_aux n ((n + 1) * acc)
termination_by n _ => n

def factorial_tail (n : ℕ) : ℕ := factorial_tail_aux n 1

#eval factorial_tail 10  -- = 3628800
#eval factorial_tail 20  -- = 2432902008176640000

/-! ## Step 5: 等価性の証明（補題） -/

lemma factorial_tail_aux_eq : ∀ n acc, 
    factorial_tail_aux n acc = factorial n * acc := by
  -- Proof strategy: Induction on n
  sorry

theorem factorial_tail_eq : ∀ n, factorial_tail n = factorial n := by
  intro n
  simp [factorial_tail]
  -- Use factorial_tail_aux_eq with acc = 1
  sorry

/-
**学習ポイント**:
  - 構造的再帰の古典的な例
  - 通常版と末尾再帰版の2つの実装
  - どちらも同じrank関数を使用
-/

end Factorial

/-! # Example 3: フィボナッチ数列 (10 minutes) -/

namespace Fibonacci

/-! ## Step 1: 目標定理の特定 -/

/-
最終目標:
  `def fib (n : ℕ) : ℕ := ...`
  n番目のフィボナッチ数を計算

定義:
  - fib 0 = 0
  - fib 1 = 1
  - fib (n+2) = fib (n+1) + fib n
-/

/-! ## Step 2: 必要条件の抽出 -/

/-
必要なもの:
- 状態: ℕ（現在の n 値）
- rank: 恒等関数（n そのもの）
- step: 2つのパターン（n+2 → n+1 と n+2 → n）
- rank減少: 両方とも減少（n+1 < n+2 かつ n < n+2）
-/

/-! ## Step 3: 最小実装 -/

/-- Rank関数: 引数そのもの -/
def fib_rank : ℕ → ℕ := id

/-- RankCore インスタンス -/
instance : ST.Ranked ℕ ℕ where
  rank := fib_rank

/-- フィボナッチ数（素朴な再帰版、非効率）-/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n
termination_by n => n

/-
効率的な線形時間版（状態として2つの値を持つ）:
-/

def fib_fast_aux : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | n + 1, a, b => fib_fast_aux n b (a + b)
termination_by n _ _ => n

def fib_fast (n : ℕ) : ℕ := fib_fast_aux n 0 1

/-! ## Step 4: 計算例 -/

-- 素朴な版（小さい値のみ実用的）
#eval fib 0   -- = 0
#eval fib 1   -- = 1
#eval fib 5   -- = 5
#eval fib 10  -- = 55
-- #eval fib 30  -- = 832040 (計算に時間がかかる)

-- 効率的な版（大きい値も高速）
#eval fib_fast 0   -- = 0
#eval fib_fast 1   -- = 1
#eval fib_fast 10  -- = 55
#eval fib_fast 30  -- = 832040
#eval fib_fast 50  -- = 12586269025

/-! ## Step 5: 等価性の証明（補題） -/

lemma fib_fast_aux_eq : ∀ n a b, 
    fib_fast_aux n a b = fib n * b + fib (n + 1) * a := by
  -- Proof strategy: Induction on n, use fib recurrence
  sorry

theorem fib_fast_eq : ∀ n, fib_fast n = fib n := by
  intro n
  simp [fib_fast]
  -- Use fib_fast_aux_eq with a = 0, b = 1
  sorry

/-
**学習ポイント**:
  - 複数の再帰呼び出しを持つ関数
  - 素朴な実装は指数時間（2^n）
  - 末尾再帰版は線形時間（O(n)）
  - どちらも同じrank関数（引数 n）で停止性を保証
  - 停止性（termination）と効率性（efficiency）は別の概念
-/

end Fibonacci

/-! # Example 4: 二分木の高さ (10 minutes) -/

namespace TreeHeight

/-! ## Step 1: 目標定理の特定 -/

/-
最終目標:
  `def tree_height (t : Tree) : ℕ := ...`
  二分木の高さを計算

木の定義:
  - Leaf: 葉（高さ 0）
  - Node: 左右の部分木を持つノード
-/

/-! ## Step 2: 必要条件の抽出 -/

/-
必要なもの:
- 状態: Tree（木の構造）
- rank: ノード数または木のサイズ
- step: Node → 左部分木 または 右部分木
- rank減少: 部分木は元の木より小さい（構造的減少）
-/

/-! ## Step 3: 最小実装 -/

/-- 二分木の定義 -/
inductive Tree (α : Type) : Type where
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α

/-- 木のサイズ（ノード数） -/
def tree_size {α : Type} : Tree α → ℕ
  | Tree.leaf => 0
  | Tree.node _ l r => 1 + tree_size l + tree_size r

/-- Rank関数: 木のサイズ -/
def tree_rank {α : Type} : Tree α → ℕ := tree_size

/-- RankCore インスタンス -/
instance {α : Type} : ST.Ranked ℕ (Tree α) where
  rank := tree_rank

/-- 木の高さ（深さ） -/
def tree_height {α : Type} : Tree α → ℕ
  | Tree.leaf => 0
  | Tree.node _ l r => 1 + max (tree_height l) (tree_height r)

/-
Leanは構造的再帰を自動認識するため、termination_byは不要だが、
明示的に書くこともできる:
-/

def tree_height_explicit {α : Type} : Tree α → ℕ
  | Tree.leaf => 0
  | Tree.node _ l r => 1 + max (tree_height_explicit l) (tree_height_explicit r)
termination_by t => tree_size t

/-! ## Step 4: 計算例 -/

open Tree

-- 単一の葉
def t1 : Tree ℕ := leaf
#eval tree_height t1  -- = 0

-- 1つのノード
def t2 : Tree ℕ := node 1 leaf leaf
#eval tree_height t2  -- = 1

-- バランスした木（高さ2）
--      1
--     / \
--    2   3
--   / \
--  4   5
def t3 : Tree ℕ := node 1 (node 2 (node 4 leaf leaf) (node 5 leaf leaf)) (node 3 leaf leaf)
#eval tree_height t3  -- = 3

-- 偏った木（高さ3）
def t4 : Tree ℕ := node 1 (node 2 (node 3 (node 4 leaf leaf) leaf) leaf) leaf
#eval tree_height t4  -- = 4

/-! ## Step 5: サイズと高さの関係（補題） -/

lemma tree_height_le_size {α : Type} : ∀ (t : Tree α), 
    tree_height t ≤ tree_size t := by
  -- Proof strategy: Induction on tree structure
  intro t
  induction t with
  | leaf => simp [tree_height, tree_size]
  | node _ l r ihl ihr =>
    simp [tree_height, tree_size]
    -- max (height l) (height r) ≤ size l + size r
    sorry

/-
**学習ポイント**:
  - 構造的再帰（structural recursion）の典型例
  - rank関数は木のサイズ
  - 部分木は常に元の木より小さい（構造的減少）
  - Leanは構造的再帰を自動認識（termination_by省略可）
  - 木の高さとサイズの関係: height ≤ size
-/

end TreeHeight

/-! # まとめ: Goal-Driven Design の威力 -/

/-
## 学習の流れ（再確認）

1. **カウントダウン**: 最も単純（rank = 引数）
2. **階乗**: 構造的再帰の基本
3. **フィボナッチ**: 複数の再帰呼び出し、効率性の問題
4. **木の高さ**: 構造的再帰、データ構造への適用

## 共通パターン

全ての例で同じアプローチ:
- Step 1: 目標定理を特定
- Step 2: 必要条件を逆算（rank関数）
- Step 3: 最小実装（RankCoreインスタンス）
- Step 4: 計算例で確認
- Step 5: 理論的な証明（lemma/theorem）

## RankCoreの役割

- 「WellFoundednessに必要な要件リスト」として機能
- 抽象理論ではなく、具体的な目標から必要性を実感
- 統一的なフレームワークで多様な例を扱える

## 次のステップ

より複雑な例へ:
- ユークリッドの互除法（GCD_Termination.lean）
- Ackermann関数（Ackermann_Termination.lean）
- マージソート、クイックソート（辞書式順序、リストの長さ）
- グラフアルゴリズム（深さ優先探索、幅優先探索）
-/

end AdditionalExamples

/-!
# RankCore と Termination: 総合学習ガイド

Goal-Driven Design アプローチによる、形式的停止性証明の実践的入門教材

## 📚 ファイル構成

### 基礎編（30分）
- `Additional_Termination_Examples.lean`: 
  - カウントダウン（5分）
  - 階乗（5分）
  - フィボナッチ数列（10分）
  - 二分木の高さ（10分）

### 応用編（30分）
- `GCD_Termination.lean`:
  - ユークリッドの互除法（20分）
  - Nat.mod_lt による rank 減少

- `Ackermann_Termination.lean`:
  - Ackermann関数（10分）
  - 辞書式順序による複雑な再帰

**総学習時間**: 約60分（全ファイル完走）

## 🎯 Goal-Driven Design の5ステップ

全ての例で統一的に使用されるアプローチ:

```lean
/-! ## Step 1: 目標定理の特定 -/
-- 最終的に証明したい定理を先に書く
-- 例: def gcd (a b : ℕ) : ℕ := ...

/-! ## Step 2: 必要条件の抽出 -/
-- 目標から逆算して必要なものを列挙
-- rank関数、step関数、rank減少の型を明示

/-! ## Step 3: 最小実装 -/
-- 抽出した必要条件のみを実装
-- RankCoreインスタンスは「チェックリスト」として使用

/-! ## Step 4: 計算例での確認 -/
-- #evalで実際に動作確認
-- rank が実際に減少することを観察

/-! ## Step 5: 目標定理の証明 -/
-- Step 3の実装を使って目標を証明
-- (lemma/theoremはsorry可)
```

## 🧩 RankCore の理論的背景

### 最小限の定義

```lean
structure Ranked (α : Type v) (X : Type u) where
  rank : X → α
```

- **RankCore = Rank関数の型クラス**
- `rank : X → α` は計算の「複雑さの測度」
- 各ステップで rank が減少すれば、停止性が保証される

### WellFoundedness との関係

```
rank関数 : X → ℕ
    ↓
layer定義 : layer n = {x | rank x ≤ n}
    ↓
WellFoundedness : ℕ の < 関係を X に引き戻す
    ↓
停止性保証 : 無限降下列は存在しない
```

## 📖 学習パスウェイ

### レベル1: 構造的再帰（15分）

**目的**: Leanの基本的なterminationを理解

- [ ] カウントダウン（rank = 引数）
- [ ] 階乗（rank = 引数、基本的な再帰）
- [ ] フィボナッチ（rank = 引数、複数の再帰呼び出し）

**重要な概念**:
- `termination_by n => n`
- 構造的減少（引数が減る）
- 末尾再帰 vs 通常の再帰

### レベル2: データ構造上の再帰（10分）

**目的**: 構造的減少を実感

- [ ] 二分木の高さ（rank = 木のサイズ）

**重要な概念**:
- 構造的再帰（structural recursion）
- 部分構造は常に小さい
- Leanの自動推論

### レベル3: 非構造的再帰（20分）

**目的**: rank関数の明示的設計

- [ ] ユークリッドの互除法（rank = 除数 b）

**重要な概念**:
- `Nat.mod_lt` による減少証明
- WellFoundedness の明示的利用
- 数学的直観（なぜこのrankなのか）

### レベル4: 辞書式順序（10分）

**目的**: 複雑な順序による停止性

- [ ] Ackermann関数（rank = 辞書式順序 (m, n)）

**重要な概念**:
- `termination_by m n => (m, n)`
- 辞書式順序のWellFoundedness
- 複数の再帰パターン

## 🔧 実装上の重要な制約

### sorry の使用規則

```lean
-- ✅ 許可: lemma, theorem
lemma my_lemma : P := by sorry
theorem my_theorem : P := by sorry

-- ❌ 禁止: def, structure, instance, example
def my_function : ℕ → ℕ := sorry  -- コンパイルエラー!
instance : MyClass := sorry        -- コンパイルエラー!

-- ✅ 必須: termination証明のヒント
def gcd (a b : ℕ) : ℕ :=
  if h : b = 0 then a
  else
    have : b % a < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
    gcd b (a % b)
termination_by b  -- 完全に記述
```

### 証明戦略のコメント

sorryを使う場合、必ず証明戦略を記述:

```lean
theorem gcd_wellfounded : WellFounded gcd_step := by
  -- Proof strategy: 
  --   1. Use invImage to lift ℕ's < to gcd_rel
  --   2. Apply Nat.lt_wfRel (ℕ is WellFounded)
  --   3. Use gcd_rank_decreases for the lifting
  sorry
```

## 📊 各例の時間配分と難易度

| 例 | 時間 | 難易度 | 主要概念 |
|---|---|---|---|
| カウントダウン | 5分 | ⭐ | 最も単純なrank |
| 階乗 | 5分 | ⭐ | 構造的再帰 |
| フィボナッチ | 10分 | ⭐⭐ | 複数の再帰、効率性 |
| 木の高さ | 10分 | ⭐⭐ | データ構造、構造的減少 |
| GCD | 20分 | ⭐⭐⭐ | 非構造的、Nat.mod_lt |
| Ackermann | 10分 | ⭐⭐⭐⭐ | 辞書式順序、複雑な再帰 |

## 🎓 教育的な価値

### 従来のアプローチ（抽象→具体）

```
RankCore理論の説明
    ↓
抽象的な定理の証明
    ↓
具体例への適用
    ↓
「なぜこんな抽象が必要？」← 学習者の疑問
```

### Goal-Driven Design（具体→抽象）

```
具体的な問題: gcdの停止性を証明したい
    ↓
必要条件を逆算: rank関数が必要
    ↓
RankCoreはその要件リスト
    ↓
「なるほど、だから必要なのか！」← 学習者の納得
```

## 💡 重要な数学的直観

### rankの選び方の原則

1. **単調減少性**: 各ステップでrankが減る
2. **下限の存在**: rankは有界（通常は ℕ）
3. **数学的意味**: 問題の本質的な複雑さを捉える

### よくあるrank関数のパターン

```lean
-- パターン1: 引数そのもの（構造的再帰）
rank (n : ℕ) = n

-- パターン2: データ構造のサイズ
rank (t : Tree α) = tree_size t

-- パターン3: 特定の成分（GCD）
rank (a, b) = b

-- パターン4: 辞書式順序（Ackermann）
rank (m, n) = (m, n)

-- パターン5: 複数の測度の組み合わせ
rank (state) = (primary_measure, secondary_measure)
```

## 🔬 理論と実践の橋渡し

### RankCoreが解決する問題

1. **Bourbakiの構造塔**: 
   - 7つの公理 → 単一のrank関数に還元
   - minLayer = rank の正当化

2. **形式検証での停止性証明**:
   - 手動のWellFoundedness証明 → 系統的なrank設計
   - 再利用可能なパターン

3. **数学の統一的理解**:
   - 確率論の停止時刻
   - 線形代数の基底選択
   - グラフ理論の距離
   - → 全てrank関数として理解可能

## 🚀 次のステップ

### さらなる応用例

- [ ] マージソート（リストの長さ）
- [ ] クイックソート（リストの長さ、辞書式）
- [ ] 深さ優先探索（訪問済みノード数）
- [ ] Collatz予想（未解決問題との関連）

### 理論的深化

- [ ] WellFounded Recursion Principle
- [ ] Accessibility Relation
- [ ] 超限帰納法（Transfinite Induction）
- [ ] Rank関数の一意性と正規形

### プロジェクト統合

- [ ] RankTower.lean との統合
- [ ] 構造塔理論との双方向対応
- [ ] Mathlibへの貢献

## 📝 参考文献

1. **Lean 4 Documentation**: 
   - Termination章
   - WellFounded章

2. **本プロジェクトの関連ファイル**:
   - `RankCore_Basic.md`: RankCoreの最小定義
   - `RankTower.lean`: rank関数と構造塔の対応
   - `ToTowerWithMin.lean`: 構造塔への変換

3. **理論的背景**:
   - Bourbaki "Théorie des Ensembles"
   - Category Theory と Galois接続
   - 形式検証とTermination証明

## ⚡ クイックスタートガイド

```bash
# 1. 基礎から学ぶ（推奨）
lean Additional_Termination_Examples.lean

# 2. 応用例を試す
lean GCD_Termination.lean
lean Ackermann_Termination.lean

# 3. 全てビルドして確認
lean --make Additional_Termination_Examples.lean GCD_Termination.lean Ackermann_Termination.lean
```

---

**Happy Proving! 🎉**

*「抽象理論から入るのではなく、具体的な目標から必要性を実感する」*
*— Goal-Driven Design の哲学*
-/

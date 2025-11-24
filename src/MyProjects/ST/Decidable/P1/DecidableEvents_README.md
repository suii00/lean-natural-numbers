# Prob/DecidableEvents.lean - 使用ガイド

## 概要

このファイルは、構造塔（Structure Tower）理論の確率論への応用の第一歩として作成されました。有限確率空間と decidable な事象の型レベル定義を提供し、将来的な DecidableFiltration（離散版フィルトレーション）への橋渡しを行います。

## ファイルの特徴

### ✅ 完全に実装された機能

1. **FiniteSampleSpace 構造体**
   - Fintype と DecidableEq を持つ有限標本空間
   - 完全な実装（sorry なし）

2. **Event の型定義**
   - Set Ω + DecidablePred の組み合わせ
   - 将来の拡張性を考慮した設計

3. **基本演算（すべて decidable）**
   - 空事象・全事象
   - 補集合・和・積・差
   - すべての演算で decidability インスタンスを完全実装

4. **具体例（#eval で計算可能）**
   - サイコロ（Fin 6）
   - コイン投げ（Bool）
   - 2個のサイコロ（Fin 6 × Fin 6）
   - 各種事象の計算例を多数含む

### ⚠️ Sorry で残されている部分

- 基本補題の証明（De Morgan の法則、分配法則など）
- ただし、すべて証明の方針をコメントで記載

## コードの構成

```
Part 1: FiniteSampleSpace の定義
  ├─ 有限性（Fintype）
  ├─ 識別可能性（DecidableEq）
  └─ cardinality と elements

Part 2: Event の型定義
  ├─ Event の abbrev 定義
  ├─ DecidableEvent 型クラス
  └─ 設計方針の詳細な説明

Part 3: 基本演算
  ├─ empty, univ
  ├─ complement, union, intersection, diff
  └─ すべての decidability インスタンス

Part 4: 基本補題
  ├─ De Morgan の法則
  ├─ 補集合の性質
  ├─ 和・積の性質
  └─ 分配法則

Part 5: 具体例
  ├─ サイコロの標本空間
  │  ├─ 偶数事象・奇数事象
  │  └─ 複合事象の例
  ├─ コイン投げ
  └─ 2個のサイコロ

Part 6: 構造塔との将来的な接続
  └─ DecidableFiltration への予告
```

## 実行例

```lean
-- サイコロの偶数事象
#eval checkEvenDice 0  -- true
#eval checkEvenDice 1  -- false
#eval checkEvenDice 2  -- true

-- コイン投げ
#eval checkHeads true   -- true
#eval checkHeads false  -- false

-- 2個のサイコロの和
#eval checkSumSeven (2, 5)  -- true  (2 + 5 = 7)
#eval checkSumSeven (3, 4)  -- true  (3 + 4 = 7)
```

すべての計算が #eval で実際に実行可能です！

## 構造塔理論との接続

### 現在のファイル（DecidableEvents.lean）
- **役割**: 有限確率空間と decidable 事象の基礎定義
- **レベル**: 最も基礎的な層

### 将来の展開

```
DecidableEvents.lean (今回)
    ↓
DecidableAlgebra.lean
    ↓
DecidableFiltration.lean ← StructureTowerWithMin のインスタンス
    ↓
ComputableStoppingTime.lean
    ↓
AlgorithmicMartingale.lean
```

### 構造塔との対応

DecidableFiltration では以下のように対応します：

- **carrier**: Event の集合
- **Index**: 時刻 ℕ
- **layer n**: 時刻 n で可観測な事象族
- **minLayer(A)**: 事象 A が初めて可観測になる時刻

これにより、停止時間を minLayer 関数で特徴づけることができます。

## 教育的価値

このファイルは以下を示しています：

1. **有限性が計算可能性をもたらすメカニズム**
   - Fintype により全要素を列挙可能
   - DecidableEq により membership 判定可能

2. **型システムによる保証**
   - decidability を型で表現
   - 誤った操作をコンパイル時に検出

3. **段階的な理論構築**
   - 最も単純な場合から始める
   - 一般化への明確な道筋

## 演習問題

ファイル末尾に以下の演習問題を含んでいます：

### 基礎問題
- De Morgan の法則の証明
- 分配法則の検証

### 応用問題
- 新しい事象の定義（素数の目、3の倍数など）
- 3個のサイコロ、カードデッキの実装

### 発展問題
- 無限事象族の扱い
- 確率測度の定義
- 構造塔への橋渡し

## 次のステップ

1. **DecidableAlgebra.lean を作成**
   - Boolean 演算で閉じた事象族
   - σ-代数の離散版

2. **確率測度の導入**
   - Event → ℚ≥0 の写像
   - 確率の公理

3. **DecidableFiltration.lean を作成**
   - StructureTowerWithMin のインスタンス
   - minLayer = 初めて可観測になる時刻

## 参考資料

- `CAT2_complete.lean`: 構造塔の完全な形式化
- `DecidableStructureTower_Examples.lean`: 構造塔の具体例
- mathlib の ProbabilityTheory モジュール

## 技術的な注意点

### なぜ Set を使うか？

- mathlib の豊富な補題を活用
- 将来の一般化（σ-代数、測度論）への拡張性
- 理論展開の自然さ

### Decidability の実装

すべての事象について DecidablePred インスタンスを提供しているため、
#eval で実際に計算可能です。これは、有限性（Fintype）があるからこそ
実現できる特性です。

### 証明の方針

sorry で残された補題は、すべて証明の方針をコメントで記載しています。
これらは mathlib の Set 理論の補題を使えば埋めることができます：

- `Set.compl_union`
- `Set.compl_inter`
- `Set.compl_compl`
- `Set.union_comm`
- `Set.inter_comm`
など

## コンパイル

```bash
lake build Prob.DecidableEvents
```

またはプロジェクトの構造に応じて適切なコマンドを使用してください。

## まとめ

このファイルは、構造塔理論の確率論への応用の**最も基礎的な層**です。
有限確率空間における decidable events の完全な実装を提供し、
将来の DecidableFiltration への明確な道筋を示しています。

すべての定義が計算可能であり、#eval で実際に動作することを確認できる
ことが、このファイルの最大の特徴です。

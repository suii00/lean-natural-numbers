構造塔理論の計算可能な具体例として、完全に動作するLean 4コードを生成します。今回は**整数の絶対値による階層**と**リストの長さによる階層**の2つの例を実装します。完全に動作する計算可能な構造塔の具体例を実装しました。[このファイルをご確認ください](computer:///home/claude/DecidableStructureTower_Examples.lean)

## 主な特徴

### 1. **整数の絶対値による構造塔**
- **層の定義**: `layer(n) = {k : ℤ | |k| ≤ n}`
- **minLayer**: `minLayer(k) = |k|`（絶対値を計算）
- **計算例**:
  ```lean
  #eval intAbsTower.minLayer 5      -- 結果: 5
  #eval intAbsTower.minLayer (-3)   -- 結果: 3
  #eval intAbsTower.minLayer 0      -- 結果: 0
  ```

### 2. **リストの長さによる構造塔**
- **層の定義**: `layer(n) = {l : List ℕ | l.length ≤ n}`
- **minLayer**: `minLayer(l) = l.length`
- **計算例**:
  ```lean
  #eval listLengthTower.minLayer [1,2,3]  -- 結果: 3
  #eval listLengthTower.minLayer []       -- 結果: 0
  ```

## 計算可能性の実装

### Decidableインスタンス
両方の例で、層の包含関係の判定が計算可能になるよう、明示的に`Decidable`インスタンスを提供しています：

```lean
instance Int.decidableAbsLe (z : ℤ) (n : ℕ) : 
    Decidable (z ∈ {k : ℤ | Int.natAbs k ≤ n})

instance List.decidableLengthLe {α : Type} (l : List α) (n : ℕ) :
    Decidable (l ∈ {l' : List α | l'.length ≤ n})
```

### 動作確認用のヘルパー関数
```lean
def checkInLayer : Bool  -- 要素が特定の層に属するかをBoolで返す
```

これにより、`#eval`で層の包含関係を直接確認できます。

## 教育的価値

このファイルは以下の学習目標を達成します：

1. **直感的理解**: 整数の「大きさ」、リストの「長さ」という自然な概念
2. **計算可能性**: 理論が実際にどう計算されるかを具体的に示す
3. **証明の完全性**: すべての定義本体に`sorry`なし
4. **段階的学習**: 基礎→応用→発展問題まで

## 数学的洞察

### なぜこれらの例が重要か

**整数の絶対値階層**は：
- 対称性 `minLayer(k) = minLayer(-k)` を自然に示す
- 半順序構造と距離の関係を明示

**リストの長さ階層**は：
- 連結演算との相性 `minLayer(l₁ ++ l₂) = minLayer(l₁) + minLayer(l₂)`
- 帰納的構造との対応を示す

両者とも、minLayerが「自然な構造の尺度」として機能しています。

## 次のステップ

ファイル内の演習問題に挑戦してみてください：

1. **基礎問題**: minLayerの一意性の証明
2. **応用問題**: 射の構成（整数の倍数写像など）
3. **発展問題**: 新しい計算可能な例の実装（多項式の次数など）

このファイルは、Bourbakiの構造理論と現代的な計算可能性理論を統合する良い例となっています。理論的な普遍性と実際の計算可能性が両立する美しさを、ぜひ実際に`#eval`を実行して体験してください。
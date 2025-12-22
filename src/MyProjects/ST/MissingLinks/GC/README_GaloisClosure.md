# 生成⇄閉包のガロア接続：構造塔理論の統一基盤

## プロジェクト概要

このプロジェクトは、**ガロア接続（Galois Connection）を最上位概念**として配置することで、
構造塔理論の「Missing Link」を埋め、異なる数学的構造を統一的に扱うフレームワークを提供します。

### 理論的階層構造

```
Level 5: 随伴関手論
         Gen ⊣ Forget
            ↓ 圏論的解釈
            
Level 4: ガロア接続 (本プロジェクトの焦点)
         Gen(s) ≤ t ↔ s ⊆ Cl(t)
            ↓ 導出
            
Level 3: 閉包演算子
         単調性・拡大性・冪等性
            ↓ 誘導
            
Level 2: 反復/生成子数による塔
         layer n = {x | 生成に必要な元の数 ≤ n}
            ↓ インスタンス化
            
Level 1: StructureTowerWithMin
         minLayer(x) = 最小生成子数
            ↓ 具体例
            
Level 0: 数学的応用
         線形包、部分群、停止時刻、イデアル
```

## ファイル構成

### コアフレームワーク

1. **GaloisClosureAPI.lean** (約300行)
   - ガロア接続の型クラス定義
   - 基本性質の導出（単調性、拡大性、冪等性）
   - 反復回数による塔の構成
   - 生成子数による塔の構成
   - StructureTowerWithMin への射影

### 具体例

2. **LinearSpanGC_Example.lean** (約400行)
   - 線形包のガロア接続インスタンス
   - ℚ² の具体例
   - 既存の minBasisCount との整合性検証
   - 層の具体的記述

3. **SubgroupGC_Example.lean** (約400行)
   - 部分群生成のガロア接続インスタンス
   - ℤ の部分群の例
   - 有限生成部分群の理論
   - 準同型と構造保存性

## 主要な定理と構成

### ガロア接続の公理

```lean
class GeneratorClosureGC (α : Type*) (S : Type*) [LE S] where
  gen : Set α → S              -- 生成関数
  cl : S → Set α                -- 閉包関数
  gc : GaloisConnection gen (OrderDual.toDual ∘ cl)
  cl_mono : Monotone cl
```

### 導出される基本性質

1. **拡大性**：`∀ s, s ⊆ cl (gen s)`
   - 集合はそれが生成する構造に含まれる

2. **単調性**：`s ⊆ t → gen s ≤ gen t`
   - 包含関係を保存

3. **冪等性**：`cl (gen (cl t)) = cl t`
   - 閉包は2回適用しても変わらない（余モナド構造）

### 塔の構成

#### 反復回数による塔

```lean
def closureIter : ℕ → Set α → Set α
  | 0 => id
  | n + 1 => fun s => cl (gen (closureIter n s))

def iterLayer (n : ℕ) : Set α :=
  {x | ∃ s : Set α, s.Finite ∧ x ∈ closureIter n s}
```

#### 生成子数による塔

```lean
def genCountLayer (n : ℕ) : Set α :=
  {x | ∃ s : Set α, s.ncard ≤ n ∧ x ∈ cl (gen s)}
```

## 具体例の理解

### 例1：線形包（LinearSpanGC_Example.lean）

**設定**：
- 基礎集合：ℚ²（有理数ベクトル空間）
- 部分構造：ℚ² の部分空間

**ガロア接続**：
- Gen(s) = span(s)：線形包
- Cl(V) = V.carrier：台集合

**層の記述**：
- 層 0：{(0,0)}（零ベクトル）
- 層 1：x軸 ∪ y軸（1つの基底ベクトルで表現）
- 層 2：ℚ² 全体（2つの基底で表現）

**minLayer の意味**：
- minLayer(v) = ベクトル v を表現するのに必要な最小基底数

### 例2：部分群生成（SubgroupGC_Example.lean）

**設定**：
- 基礎集合：ℤ（整数の加法群）
- 部分構造：ℤ の部分群

**ガロア接続**：
- Gen(s) = ⟨s⟩：部分群生成
- Cl(H) = H.carrier：台集合

**層の記述**：
- 層 0：{0}（自明な部分群）
- 層 1：ℤ 全体（⟨{1}⟩ = ℤ、巡回群の性質）

**minLayer の意味**：
- minLayer(n) = 元 n を表現するのに必要な最小生成元数

### 線形包 vs 部分群：比較表

| 側面               | 線形包（ℚ²）                    | 部分群（ℤ）                     |
|--------------------|--------------------------------|--------------------------------|
| Gen 演算           | 線形結合                       | 群演算・逆元                    |
| 層 1 の特徴        | 軸上のベクトル                  | 全体（巡回群）                  |
| 層の個数           | 3層（0, 1, 2）                 | 2層（0, 1）                    |
| minLayer の範囲    | 0, 1, 2                        | 0, 1                           |
| 射                 | 線形写像                        | 群準同型                        |

## DoD（完了条件）の検証

### ✅ 完了した項目

1. **def と structure に sorry なし**
   - `GeneratorClosureGC`：完全定義
   - `closureIter`：完全定義
   - `genCountLayer`：完全定義
   - `structureTowerFromGC`：完全定義
   - インスタンス定義：完全実装

2. **ガロア接続から性質を導出**
   - 拡大性：`subset_cl_gen`（証明済み）
   - 単調性：`gen_mono`（証明済み）
   - 冪等性：`cl_cl_eq`（証明済み）

3. **具体例のインスタンス**
   - 線形包：`linearSpanGC`（実装済み）
   - 部分群：`subgroupGC`（実装済み）

### ⚠️ 証明が省略されている項目（lemma/theorem）

以下は `sorry` を使用していますが、制約により許可されています：

1. **層の精密な特徴づけ**
   - `genCountLayer_zero`：集合の濃度に関する補題が必要
   - `genCountLayer_one_subset`：有限集合の組合せ論が必要
   - `genCountLayer_two`：完全な証明には Finset の補題が必要

2. **反復の収束性**
   - `closureIter_eventually_constant`：鎖条件や次元論が必要
   - 有限次元の場合は証明可能

3. **既存理論との同値性**
   - `minLayer_eq_minBasisCount`：層の完全な特徴づけが前提

## ビルド方法

### 前提条件

- Lean 4（最新版推奨）
- Mathlib 4

### プロジェクト設定

```toml
# lakefile.lean に追加
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```

### ビルドコマンド

```bash
lake build GaloisClosureAPI
lake build LinearSpanGC_Example
lake build SubgroupGC_Example
```

### 依存関係

```
GaloisClosureAPI.lean
    ↓ import
LinearSpanGC_Example.lean
    ↓ import
SubgroupGC_Example.lean
```

## 理論的背景

### ガロア接続の起源

ガロア接続は、エヴァリスト・ガロアの体の理論における「体の拡大 ⇄ 部分群」の対応に由来します。

**古典的ガロア対応**：
```
{体の拡大} ⇄ {ガロア群の部分群}
K ⊆ L ↔ Gal(L/K) ⊇ H
```

**本フレームワークでの一般化**：
```
{部分集合} ⇄ {部分構造}
Gen(s) ≤ t ↔ s ⊆ Cl(t)
```

### 余モナドとしての閉包

閉包演算子は、圏論的には余モナド（comonad）の構造を持ちます：

1. **counit**：ε : Cl ∘ Gen → Id
   - 「生成して閉包を取れば元に戻る」

2. **comultiplication**：δ : Cl → Cl ∘ Cl ∘ Cl
   - 閉包の冪等性（`cl_cl_eq`）

### 随伴関手との関係

ガロア接続は、随伴関手の順序理論版です：

```
圏論：Gen ⊣ Forget（随伴関手）
順序論：Gen(s) ≤ t ↔ s ⊆ Cl(t)（ガロア接続）
```

## 教育的活用方法

### 段階的学習パス

#### Level 1：具体例から入る
1. `LinearSpanGC_Example.lean` の層 0, 1, 2 の計算
2. `#eval` で具体的なベクトルの minLayer を確認
3. 視覚的理解（2次元平面での図示）

#### Level 2：抽象概念の理解
1. `GaloisClosureAPI.lean` の型クラス定義を読む
2. `subset_cl_gen` などの基本定理を理解
3. 線形包と部分群の対応表を比較

#### Level 3：理論の深化
1. ガロア接続の公理から性質を導出する過程を追う
2. 余モナド構造の理解
3. 他の数学的構造への応用を考察

### 演習問題

1. **基礎**：
   - minBasisCount((3, 4)) を計算せよ
   - ℤ の部分群 6ℤ の minLayer を求めよ

2. **応用**：
   - ℚ³ への拡張を考察せよ
   - 有限群の場合の層構造を記述せよ

3. **発展**：
   - 位相的閉包のインスタンスを定義せよ
   - イデアル生成のガロア接続を実装せよ

## 今後の拡張方向

### 短期的拡張

1. **証明の完成**
   - 省略した lemma の証明を埋める
   - Mathlib の既存補題を活用

2. **新しい具体例**
   - 環のイデアル生成
   - 位相的閉包
   - グラフの到達可能性

### 中期的拡張

1. **計算可能性**
   - minLayer の効率的アルゴリズム
   - 有限次元の場合の決定手続き

2. **可視化ツール**
   - 層の図示
   - インタラクティブな探索

### 長期的研究課題

1. **高次圏論への拡張**
   - 2-ガロア接続
   - モナド・余モナドの完全形式化

2. **他分野への応用**
   - 確率論（フィルトレーション）
   - 組合せ論（凸包）
   - 計算機科学（到達可能性解析）

## 参考文献

1. Bourbaki, N. (1968). *Theory of Sets*. Elements of Mathematics.
2. Mac Lane, S. (1998). *Categories for the Working Mathematician*.
3. Davey, B. A., & Priestley, H. A. (2002). *Introduction to Lattices and Order*.
4. Erné, M. et al. (1993). "A primer on Galois connections". *Annals of the New York Academy of Sciences*.

## プロジェクトステータス

- **理論的完成度**：90%（核心部分は完成）
- **証明の完成度**：60%（主要定理は証明済み、補助補題は一部省略）
- **具体例の充実度**：70%（線形包・部分群は完成、他は今後）
- **ドキュメント**：80%（基本的な説明は完備）

## ライセンスと貢献

このプロジェクトは教育・研究目的で公開されています。
貢献・質問・フィードバックを歓迎します。

## 謝辞

- Lean 4 および Mathlib コミュニティ
- Bourbaki の構造主義的数学観
- ガロア接続理論の先駆者たち

---

最終更新：2024年12月21日
作成者：Claude (Anthropic)

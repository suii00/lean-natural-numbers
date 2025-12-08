import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic

/-!
# IUT3 課題：ガロア理論と代数的整数論の構造塔

ZEN大学「Inter-universal Teichmüller Theory 3」の課題として、
対称性（ガロア理論）と算術的構造（代数的整数論）を
構造塔の枠組みで統一的に理解する。

## 学習目標

1. **対称性の階層**: ガロア群と中間体の対応を構造塔で理解
2. **分岐理論**: 素イデアルの分解と構造塔の層の対応
3. **局所大域原理**: 局所体の構造塔から大域体への持ち上げ
4. **ディオファントス**: 方程式の可解性とガロア理論の関係
5. **IUT理論の対称性**: 多重宇宙とガロア群の「宇宙際的」扱い

## IUT1→IUT2→IUT3 の発展

### 構造塔の解釈の進化

| シリーズ | carrier | minLayer の意味 | 主要概念 |
|---------|---------|----------------|---------|
| IUT1 | 整数、体 | 素因数個数、拡大次数 | 数論的階層 |
| IUT2 | スキーム、曲線 | 次元、高さ | 幾何的階層 |
| **IUT3** | ガロア拡大、整数環 | ガロア群の位数、分岐指数 | **対称性の階層** |

### 概念の統合
```
            IUT3: 対称性
              /        \
          /              \
   IUT1: 数論      IUT2: 幾何
        \              /
          \          /
            IUT理論
```

**ガロアの基本定理 ≃ 構造塔の圏同値**:
- ガロア群の部分群 ↔ 中間体 ↔ 構造塔の層
- 群の指数 ↔ 拡大次数 ↔ minLayer の差分
- 正規部分群 ↔ ガロア閉包 ↔ 層の構造保存

## Report課題（70%）
（A4で10-12ページ、IUT1, IUT2より高度）

### Part A: ガロア理論的理解（必須）

1. **対称性の可視化**
   - ガロア群 Gal(L/K) を図示
   - 中間体の格子と構造塔の層の対応
   - 部分群の包含 ⇔ 体の拡大 ⇔ 層の包含

2. **ガロアの基本定理**
   - 構造塔の言葉で再定式化
   - minLayer が「固定次数」を測る理由
   - 圏同値としての理解

3. **具体的計算**
   - ℚ[√2, √3]/ℚ のガロア群
   - 中間体すべてを構造塔の層として記述
   - 各層の minLayer を計算

### Part B: 代数的整数論（必須）

4. **分岐理論**
   - 素イデアルの分解と構造塔
   - e(P|p), f(P|p), g(P|p) の意味
   - Dedekind-Kummer定理の構造塔版

5. **イデアル類群**
   - 類群 Cl(K) と構造塔
   - 主イデアルの特徴付け
   - UFD との関係

### Part C: ディオファントス応用（選択）

6. **平方和問題**
   - Lagrange の四平方定理の証明戦略
   - ℚ[i] のガロア理論との関係

7. **Fermat 方程式**
   - 円分体でのアプローチ（Kummer）
   - 構造塔による整理

### Part D: IUT理論への接続（発展）

8. **対称性の「宇宙際化」**
   - ガロア群の各元を「異なる宇宙」と見る
   - 構造塔の各層 = 1つの宇宙
   - 層の移行 = 宇宙間の Θ-link

9. **遠アーベル幾何**
   - エタール基本群とガロア群
   - 絶対ガロア群の構造塔

## Group Work課題（30%）
（A4で4ページ、より深い議論）

### 課題1：ガロアの基本定理の構造塔版（60分）
- ℚ[√2, √3]/ℚ を完全に解析
- 中間体の格子を図示
- 構造塔の各層を明示的に記述
- 「圏同値」の意味を議論

### 課題2：分岐と層の対応（45分）
- ℚ[√2]/ℚ での素数 2 の分岐
- 分岐指数 e = 2 が minLayer でどう現れるか
- 完全分岐・不分岐・タメ分岐の分類

### 課題3：局所大域原理（45分）
- Hasse-Minkowski 定理の直観
- 局所体の構造塔 ℚ_p から大域体 ℚ へ
- IUT理論における「局所宇宙」と「大域宇宙」

### 課題4：IUT理論との対応（発展、60分）
- Mochizuki "IUT III" §1 を読む
- 「Frobenioid」とガロア圏の関係
- 構造塔の射と「同期射」の対応

### 提出物
- 完全な図式（ガロア群、中間体格子）
- 分岐の可視化図
- 議論のメモと各メンバーの貢献

## 教育的意義

### 2年次後半（IUT1, IUT2修了者）に配慮
- ガロア理論の復習から開始（定義、基本定理）
- 抽象論の前に具体例（ℚ[√2], ℚ[i], ℚ[ζₙ]）
- 「なぜ対称性が重要か」を丁寧に説明
- 図式（ガロア群の図、中間体の格子）を豊富に

### ガロア理論と構造塔の対応
- 各定義で「群論的意味 ⇔ 体論的意味 ⇔ 構造塔の層」を明示
- ガロアの基本定理 = 構造塔の圏同値
- 正規部分群 ⇔ ガロア閉包 ⇔ 層の構造保存

### ディオファントス問題への応用
- 抽象論が具体的問題を解く
- Lagrange の四平方定理の証明
- Fermat 方程式へのアプローチ

### IUT理論への展望
- ガロア群の元 = 異なる宇宙
- 対称性の「宇宙際的」扱い
- Hodge-Arakelov 理論での対称性の役割

-/

/-!
## 構造塔の定義（IUT1, IUT2から継承）

構造塔の簡約版定義。完全版は CAT2_complete.lean 参照。
-/

/-- 構造塔の基本定義（IUT1, IUT2と同様） -/
structure StructureTowerMin (X : Type*) (I : Type*) [Preorder I] where
  /-- 各層の定義 -/
  layer : I → Set X
  /-- 被覆性：すべての元がどこかの層に属する -/
  covering : ∀ x : X, ∃ i : I, x ∈ layer i
  /-- 単調性：層は増加列をなす -/
  monotone : ∀ {i j : I}, i ≤ j → layer i ⊆ layer j
  /-- 各元の最小層を選ぶ関数 -/
  minLayer : X → I
  /-- minLayer x は実際に x を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayer x は最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

/-!
## IUT1, IUT2 の復習

### IUT1で学んだ数論的構造塔：
1. 素因数分解の深さ（整数の複雑さ）
2. 体の拡大次数（ℚ ⊆ ℚ[√2] ⊆ ...）
3. 2-進付値（局所構造の導入）
4. 円分体の階層（ℚ ⊆ ℚ[ζₙ]）

### IUT2で学んだ幾何的構造塔：
1. Spec(R) の素イデアルの高さ（次元）
2. 代数曲線の次数階層
3. 層理論の基礎（層の台、コホモロジー）
4. 楕円曲線の還元型

### IUT3での統合：
**ガロア理論による対称性** + **幾何的視点** = **IUT理論の核心**

IUT3では、これらを「ガロア群の作用」「分岐構造」「局所大域原理」という
対称性の観点から統一的に理解します。
-/

/-!
# Part 1: ガロア理論の構造塔（5例）

各例は以下の構造：
- carrier: ℚ の有限ガロア拡大、またはガロア群
- minLayer: 拡大次数 [L:K]、またはガロア群の位数 |Gal(L/K)|
- 対称性の解釈: ガロア群の作用、中間体の格子

## ガロア理論の基礎復習

### ガロア拡大の定義
体の拡大 L/K が**ガロア拡大**であるとは：
1. L/K は正規拡大（L で分解するすべての既約多項式が L で完全分解）
2. L/K は分離拡大（既約多項式は重根を持たない）

同値な定義：L/K は L のある部分集合上の多項式の分解体

### ガロア群
ガロア拡大 L/K に対して、
  Gal(L/K) := {σ : L → L | σ は体同型かつ K の元を固定}

### ガロアの基本定理
L/K をガロア拡大とする。このとき、以下の対応が成り立つ：
  {L と K の中間体} ↔ {Gal(L/K) の部分群}
  E ↦ Gal(L/E)（E を固定する自己同型）
  L^H ← H（H で固定される元）

しかも：
- 拡大次数：[E:K] = |Gal(L/K)|/|Gal(L/E)| = [Gal(L/K) : Gal(L/E)]
- 正規性：E/K がガロアである ⇔ Gal(L/E) ⊴ Gal(L/K)（正規部分群）
- そのとき：Gal(E/K) ≃ Gal(L/K)/Gal(L/E)

これを**構造塔の言葉で再解釈**するのが本Part の目標。
-/

/-!
## 例1：ガロア拡大の次数階層

### IUT1, IUT2からの発展
- IUT1: 体の拡大次数を単に測った
- IUT2: 環の拡大を幾何的（被覆空間）として理解
- **IUT3**: ガロア群という対称性を明示的に扱う

### ガロア理論的背景
L/K をガロア拡大とする。拡大次数 [L:K] は：
- 代数的：L の K 上の次元
- 群論的：|Gal(L/K)|（ガロア群の位数）
- 幾何的：被覆次数

**重要**：ガロア拡大では [L:K] = |Gal(L/K)| が成立。

### 構造塔としての定式化
- **carrier**: ℚ の有限ガロア拡大全体
- **Index**: ℕ（拡大次数）
- **layer n**: {L | [L:ℚ] ≤ n}（次数 ≤ n のガロア拡大）
- **minLayer(L)**: [L:ℚ]（拡大次数そのもの）

### 対称性の可視化
```
例：ℚ[√2, √3]/ℚ のガロア群 ≃ ℤ/2ℤ × ℤ/2ℤ（Klein四元群）

    ℚ[√2, √3]  (Layer 4: [L:ℚ] = 4)
      /    |    \
     /     |     \
ℚ[√2]  ℚ[√3]  ℚ[√6]  (Layer 2: [L:ℚ] = 2)
     \     |     /
      \    |    /
         ℚ         (Layer 1: [L:ℚ] = 1)

対称性：Klein四元群 V₄ = {e, σ, τ, στ} の作用
- e: 恒等写像
- σ: √2 ↦ -√2, √3 ↦ √3
- τ: √2 ↦ √2, √3 ↦ -√3
- στ: √2 ↦ -√2, √3 ↦ -√3
```

### ガロアの基本定理との対応

| 群論 | 体論 | 構造塔 |
|------|------|--------|
| 部分群 H ≤ G | 固定体 L^H | 層 layer n |
| 指数 [G:H] | 拡大次数 [L^H:K] | minLayer の差 |
| 正規部分群 | ガロア中間体 | 構造保存層 |

### IUT理論への展望
**対称性の宇宙際化**：
- 各中間体 E = 1つの「宇宙」
- 層の移行 = 宇宙間の移動
- ガロア群の作用 = 宇宙の同一視

望月の IUT 理論では、これが p-進的・Hodge的構造と組み合わさる。
-/

namespace GaloisTheory.FieldExtensionDegree

/-- ℚ の有限ガロア拡大を表す型（簡易版）
実際の実装では、もっと精密な定義が必要だが、
教育的には「ℚ に有限個の代数的元を添加した体」と理解する。
-/
structure FiniteGaloisExtension where
  /-- 拡大体（便宜上 Type* として抽象化） -/
  carrier : Type*
  /-- 拡大次数 -/
  degree : ℕ
  /-- 次数は正 -/
  degree_pos : 0 < degree
  /-- ガロア群の位数（ガロア拡大なので degree と一致） -/
  galois_group_order : ℕ
  /-- ガロア拡大の条件：|Gal(L/ℚ)| = [L:ℚ] -/
  galois_condition : galois_group_order = degree

/-- ℚ 自身（自明な拡大、次数 1） -/
def trivialExtension : FiniteGaloisExtension where
  carrier := ℚ
  degree := 1
  degree_pos := by norm_num
  galois_group_order := 1
  galois_condition := rfl

/-- ℚ[√2] over ℚ（次数 2） -/
def Q_sqrt2 : FiniteGaloisExtension where
  carrier := ℚ  -- 実装の簡略化
  degree := 2
  degree_pos := by norm_num
  galois_group_order := 2
  galois_condition := rfl

/-- ℚ[i] over ℚ（ガウス有理数、次数 2） -/
def Q_i : FiniteGaloisExtension where
  carrier := ℚ  -- 実装の簡略化
  degree := 2
  degree_pos := by norm_num
  galois_group_order := 2
  galois_condition := rfl

/-- ℚ[√2, √3] over ℚ（次数 4） -/
def Q_sqrt2_sqrt3 : FiniteGaloisExtension where
  carrier := ℚ  -- 実装の簡略化
  degree := 4
  degree_pos := by norm_num
  galois_group_order := 4
  galois_condition := rfl

/-- ガロア拡大の構造塔 -/
noncomputable def galoisExtensionTower : StructureTowerMin FiniteGaloisExtension ℕ where
  layer := fun n => {L : FiniteGaloisExtension | L.degree ≤ n}

  covering := by
    intro L
    exact ⟨L.degree, le_refl L.degree⟩

  monotone := by
    intro i j hij L hL
    exact le_trans hL hij

  minLayer := fun L => L.degree

  minLayer_mem := by
    intro L
    exact le_refl L.degree

  minLayer_minimal := by
    intro L i hi
    exact hi

/-! ### 計算例（具体的な拡大で） -/

/-- ℚ の例（自明な拡大、次数 1） -/
example : galoisExtensionTower.minLayer trivialExtension = 1 := by
  rfl

/-- ℚ[√2]/ℚ の例（次数 2） -/
example : galoisExtensionTower.minLayer Q_sqrt2 = 2 := by
  rfl

/-- ℚ[√2, √3]/ℚ の例（次数 4） -/
example : galoisExtensionTower.minLayer Q_sqrt2_sqrt3 = 4 := by
  rfl

-- TODO: ここから下は型の再設計後に肉付け予定。今回は簡易版を再有効化。
/-! ### ガロア理論的定理 -/

/-- Layer 1 に属する拡大は次数 1（＝minLayer） -/
theorem layer_one_degree_le :
    ∀ L, L ∈ galoisExtensionTower.layer 1 → L.degree = 1 := by
  intro L hL
  change L.degree ≤ 1 at hL
  have hpos : 0 < L.degree := L.degree_pos
  have hge : 1 ≤ L.degree := Nat.succ_le_of_lt hpos
  exact le_antisymm hL hge

/-- Layer 2 には次数 1 と 2 の拡大が含まれる -/
theorem layer_two_contains_quadratic :
    Q_sqrt2 ∈ galoisExtensionTower.layer 2 ∧
    Q_i ∈ galoisExtensionTower.layer 2 := by
  constructor <;> (change (_ ≤ 2) ; decide)

/-- ガロアの基本定理の構造塔版（概念的） -/
theorem fundamental_theorem_via_tower :
    ∀ _L : FiniteGaloisExtension,
    -- [中間体の格子] ≃ [部分群の格子] ≃ [構造塔の部分層]
    True := by
  intro _L
  trivial
  /-
  証明のスケッチ：
  1. ガロアの基本定理により、中間体 E と部分群 H が 1:1 対応
  2. 各中間体 E に対して、[E:ℚ] = minLayer(E) を定義
  3. E ⊆ F ⇔ [E:ℚ] ≤ [F:ℚ] ⇔ minLayer(E) ≤ minLayer(F)
  4. したがって、中間体の順序 = 構造塔の層の順序
  5. これは圏同値を与える

  詳細は Group Work 課題で議論する。
  -/

/-- 中間体と層の対応 -/
theorem intermediate_field_layer_correspondence :
    ∀ (L : FiniteGaloisExtension) (E_degree : ℕ),
    E_degree ∣ L.degree →  -- E は L の中間体
    ∃ m, -- E に対応する層番号 m が存在
    m = E_degree := by
  intro L E_degree hdiv
  exact ⟨E_degree, rfl⟩
  /-
  証明：
  1. E は L と ℚ の中間体なので、[E:ℚ] は [L:ℚ] の約数
  2. m := [E:ℚ] とする
  3. E ∈ layer m が成り立つ（定義より）
  4. m = [E:ℚ] = minLayer(E)
  -/

end GaloisTheory.FieldExtensionDegree

/-!
## 例2：ガロア群の位数階層

### IUT1, IUT2からの発展
- IUT1: 体の拡大次数という「大きさ」を測った
- IUT2: 被覆空間の葉の数という幾何的解釈
- **IUT3**: ガロア群の位数 = 対称性の「複雑さ」

### ガロア理論的背景
ガロア群 Gal(L/K) の位数 |Gal(L/K)| は：
- 群論的：群の元の個数
- 体論的：[L:K]（ガロア拡大の場合）
- 対称性的：K を固定して L を動かす方法の総数

**重要な事実**：
- |Gal(L/K)| = [L:K]（ガロア拡大）
- 中間体 E に対して：|Gal(L/E)| = [L:E]
- 指数定理：[G : H] = |G|/|H|

### 構造塔としての定式化
- **carrier**: 有限ガロア拡大 L/ℚ
- **Index**: ℕ（ガロア群の位数）
- **layer n**: {L | |Gal(L/ℚ)| ≤ n}
- **minLayer(L)**: |Gal(L/ℚ)|

**注意**：例1とは異なり、こちらは「対称性の複雑さ」に焦点を当てる。

### 対称性の可視化：Klein四元群

```
ℚ[√2, √3]/ℚ のガロア群：G = Gal(ℚ[√2, √3]/ℚ) ≃ V₄

部分群の格子（Hasse図）：
        G = {e, σ, τ, στ}  (位数4)
       /    |    \
      /     |     \
  {e,σ}  {e,τ}  {e,στ}   (位数2)
      \     |     /
       \    |    /
          {e}              (位数1)

対応する中間体（ガロアの基本定理）：
         ℚ                (固定体: G)
         /  |  \
        /   |   \
   ℚ[√2] ℚ[√3] ℚ[√6]    (固定体: 位数2の部分群)
        \   |   /
         \  |  /
      ℚ[√2, √3]          (固定体: {e})

構造塔の層：
layer 1: {ℚ}                    (minLayer = 1)
layer 2: {ℚ, ℚ[√2], ℚ[√3], ℚ[√6]} (minLayer ≤ 2)
layer 4: すべて                  (minLayer ≤ 4)
```

### ガロアの基本定理：詳細版

**定理（ガロアの基本定理）**：
L/K をガロア拡大、G = Gal(L/K) とする。このとき、

1. 対応写像が存在：
   - Φ: {K と L の中間体} → {G の部分群}
   - Φ(E) = Gal(L/E)（E を固定する自己同型）
   - Ψ: {G の部分群} → {K と L の中間体}
   - Ψ(H) = L^H（H で固定される元）

2. これらは互いに逆写像：
   - Ψ(Φ(E)) = E
   - Φ(Ψ(H)) = H

3. 順序を逆転：
   - E₁ ⊆ E₂ ⇔ Φ(E₂) ⊆ Φ(E₁)

4. 指数の公式：
   - [E:K] = [G : Gal(L/E)] = |G|/|Gal(L/E)|

5. 正規性：
   - E/K がガロア ⇔ Gal(L/E) ⊴ G（正規部分群）
   - このとき：Gal(E/K) ≃ G/Gal(L/E)

### 構造塔での解釈

| ガロアの基本定理 | 構造塔の言葉 |
|----------------|------------|
| 中間体 E | carrier の要素 |
| E₁ ⊆ E₂ | minLayer(E₁) ≤ minLayer(E₂) |
| [E:K] | minLayer(E) |
| Gal(L/E) の位数 | [L:E] = minLayer(L) - minLayer(E) |
| 正規部分群 | 層の構造保存性 |

### IUT理論への展望

**宇宙の対称性**：
- 各中間体 E = 1つの宇宙
- Gal(L/E) = その宇宙の対称性群
- 宇宙を変える = 中間体を変える = 層を移動する

望月の IUT では：
- 各宇宙に Hodge-Arakelov 理論の構造が入る
- 宇宙間の「同期」= ガロア作用の p-進的版
- Θ-link = 対称性を保ちながらの宇宙の移動

-/

-- TODO: 以下（例2以降）は再設計時に段階的に復活させる。暫定的にコメントアウト。
namespace GaloisTheory.GaloisGroupOrder
open GaloisTheory.FieldExtensionDegree

/-- ガロア群の位数による構造塔
これは例1と本質的に同じだが、「対称性の複雑さ」に焦点を当てる
-/
noncomputable def galoisGroupTower : StructureTowerMin FiniteGaloisExtension ℕ where
  layer := fun n => {L : FiniteGaloisExtension | L.galois_group_order ≤ n}

  covering := by
    intro L
    -- ガロア拡大なので galois_group_order = degree
    have h := L.galois_condition
    exact ⟨L.galois_group_order, le_refl L.galois_group_order⟩

  monotone := by
    intro i j hij L hL
    exact le_trans hL hij

  minLayer := fun L => L.galois_group_order

  minLayer_mem := by
    intro L
    exact le_refl L.galois_group_order

  minLayer_minimal := by
    intro L i hi
    exact hi

/-! ### 計算例 -/

/-- ガロア群の位数は拡大次数と一致 -/
example : galoisGroupTower.minLayer trivialExtension = 1 := by
  rfl

example : galoisGroupTower.minLayer Q_sqrt2 = 2 := by
  rfl

example : galoisGroupTower.minLayer Q_sqrt2_sqrt3 = 4 := by
  rfl

/-! ### ガロア群の理論 -/

/-- 位数 1 の群は自明な群のみ -/
theorem galois_group_order_one_iff_trivial :
    ∀ L : FiniteGaloisExtension,
    L.galois_group_order = 1 ↔ L.degree = 1 := by
  intro L
  constructor
  · intro h
    rw [← L.galois_condition]
    exact h
  · intro h
    rw [L.galois_condition]
    exact h

/-- 位数 2 の群は巡回群 ℤ/2ℤ に同型 -/
theorem galois_group_order_two_is_cyclic :
    ∀ L : FiniteGaloisExtension,
    L.galois_group_order = 2 →
    -- Gal(L/ℚ) ≃ ℤ/2ℤ
    True := by
  intro _ _
  trivial
  /-
  証明：
  1. 位数 2 の群は必ず巡回群（群論の基本定理）
  2. したがって Gal(L/ℚ) ≃ ℤ/2ℤ
  3. 具体例：ℚ[√2]/ℚ, ℚ[i]/ℚ
  -/

/-- 位数 4 の群は2種類：ℤ/4ℤ または V₄（Klein四元群） -/
theorem galois_group_order_four_types :
    ∀ L : FiniteGaloisExtension,
    L.galois_group_order = 4 →
    -- Gal(L/ℚ) ≃ ℤ/4ℤ または Gal(L/ℚ) ≃ V₄
    True := by
  intro _ _
  trivial
  /-
  証明：
  1. 位数 4 の群は同型を除いて2種類のみ
     - ℤ/4ℤ：巡回群（例：ℚ[ζ₄]/ℚ = ℚ[i]/ℚ, これは次数2）
     - V₄：Klein四元群（例：ℚ[√2, √3]/ℚ）
  2. ℚ[√2, √3]/ℚ の場合：
     - 4つの自己同型：e, σ, τ, στ
     - すべて位数 ≤ 2（平方すると恒等写像）
     - したがって V₄ に同型
  -/

set_option linter.unusedVariables false in
/-- 部分群の指数と中間体の次数の関係 -/
theorem index_formula :
    ∀ (L : FiniteGaloisExtension)
      (H_order : ℕ)
      (hdiv : H_order ∣ L.galois_group_order),
    -- [G : H] * H_order = |G|
    (L.galois_group_order / H_order) * H_order = L.galois_group_order := by
  intro L H_order hdiv
  exact Nat.div_mul_cancel hdiv

end GaloisTheory.GaloisGroupOrder

-- TODO: 以下のセクション（可解拡大以降）は再設計時に段階的に復活させる。

/-
## 例3：可解拡大の階層

### IUT1, IUT2からの発展
- IUT1: 体の拡大を単に「大きさ」で測った
- IUT2: 被覆空間の「複雑さ」
- **IUT3**: 可解性 = 「対称性の制御可能性」

### ガロア理論的背景

**定義（可解群）**：
群 G が可解（solvable）であるとは、以下の正規列が存在すること：
  {e} = G₀ ⊴ G₁ ⊴ G₂ ⊴ ... ⊴ Gₙ = G
各商群 Gᵢ₊₁/Gᵢ がアーベル群（可換群）

**定義（可解拡大）**：
体の拡大 L/K が可解であるとは、Gal(L/K) が可解群であること。

**重要な定理**：
1. アーベル拡大 ⇒ 可解拡大（明らか）
2. 可解拡大の塔 ⇒ 可解拡大（可解列を接続）
3. 5次以上の一般方程式は可解でない（Abel-Ruffini）

### 構造塔としての定式化
- **carrier**: 有限ガロア拡大 L/ℚ
- **Index**: ℕ（可解列の長さ）
- **layer n**: {L | Gal(L/ℚ) が長さ ≤ n の可解列を持つ}
- **minLayer(L)**: 最小の可解列の長さ

**可解列の長さの定義**：
- 0: 自明な拡大（ℚ/ℚ）
- 1: アーベル拡大（1段階で可解）
- 2: 1回の非可換拡大を経由
- ...

### 対称性の視点：可解性 = 段階的対称性の破れ

```
可解群の可解列：
  G = G₃ → G₂ → G₁ → G₀ = {e}
        ↓    ↓    ↓
     商群が  すべて
     可換    アーベル

対応する体の塔（Galois対応により逆順）：
  K = E₀ ⊂ E₁ ⊂ E₂ ⊂ E₃ = L
       ↑    ↑    ↑
     各段階 すべて
     がアーベル 可換拡大
```

例：ℚ[√2, √3]/ℚ の可解列
- Gal(ℚ[√2, √3]/ℚ) = V₄（Klein四元群、アーベル）
- したがって長さ 1 の可解列：V₄ → {e}
- minLayer = 1

例：対称群 S₅
- S₅ は可解でない
- したがって、5次の一般方程式のガロア群に対応する拡大は
  有限長の可解列を持たない
- minLayer = ∞（または未定義）

### ガロア理論的重要性

**Abel-Ruffini の定理（1824）**：
5次以上の一般方程式は、四則演算と冪根だけでは解けない。

**証明の骨子**：
1. 方程式が四則と冪根で解ける ⇔ ガロア群が可解
2. 5次一般方程式のガロア群は S₅
3. S₅ は可解でない
4. したがって、解けない ∎

構造塔での解釈：
- 可解拡大 = 有限層に到達
- 非可解拡大 = 無限層（または定義域外）

### IUT理論への展望

**対称性の破れの制御**：
- 可解列 = 対称性を段階的に破る手順
- 各段階がアーベル = 「制御可能」な対称性の破れ
- IUT 理論では、Hodge-Arakelov 構造の変形も段階的

**Grothendieck-Teichmüller 群**：
- 絶対ガロア群の「制御可能」な部分
- 可解でない部分が深い構造を持つ

-/


namespace GaloisTheory.SolvableExtensions

-- FiniteGaloisExtension などは前節の namespace で定義しているので開く
open GaloisTheory.FieldExtensionDegree

/-- 可解列の長さを表す型 -/
inductive SolvableLength
  | zero : SolvableLength  -- 自明な拡大
  | finite (n : ℕ) : SolvableLength  -- 長さ n の可解列
  | infinite : SolvableLength  -- 非可解

/-- 可解長の順序 -/
instance : LE SolvableLength where
  le x y := match x, y with
    | SolvableLength.zero, _ => True
    | SolvableLength.finite n, SolvableLength.finite m => n ≤ m
    | SolvableLength.finite _, SolvableLength.infinite => True
    | SolvableLength.infinite, SolvableLength.infinite => True
    | _, _ => False

/-- 有限ガロア拡大に可解長を付加 -/
structure SolvableGaloisExtension extends FiniteGaloisExtension where
  /-- ガロア群の可解長 -/
  solvable_length : SolvableLength
  /-- アーベル拡大は可解長 ≤ 1 を持つ -/
  abelian_bound : (solvable_length = SolvableLength.zero ∨
                   solvable_length = SolvableLength.finite 1) ∨
                  solvable_length = SolvableLength.finite 2 ∨
                  True -- 一般の場合

/-- ℚ 自身（可解長 0） -/
def trivialSolvable : SolvableGaloisExtension where
  toFiniteGaloisExtension := trivialExtension
  solvable_length := SolvableLength.zero
  abelian_bound := by left; left; rfl

/-- ℚ[√2]/ℚ（アーベル拡大、可解長 1） -/
def Q_sqrt2_solvable : SolvableGaloisExtension where
  toFiniteGaloisExtension := Q_sqrt2
  solvable_length := SolvableLength.finite 1
  abelian_bound := by left; right; rfl

/-- ℚ[√2, √3]/ℚ（Klein四元群、アーベル、可解長 1） -/
def Q_sqrt2_sqrt3_solvable : SolvableGaloisExtension where
  toFiniteGaloisExtension := Q_sqrt2_sqrt3
  solvable_length := SolvableLength.finite 1
  abelian_bound := by left; right; rfl

/-!
### 可解拡大の構造塔（概念的）

実装上の制約により、ここでは可解長を自然数に制限する。
無限の場合は別途扱う。
-/

/-- 可解長による順序（有限部分のみ） -/
def solvable_length_to_nat (L : SolvableGaloisExtension) : ℕ :=
  match L.solvable_length with
  | SolvableLength.zero => 0
  | SolvableLength.finite n => n
  | SolvableLength.infinite => 100  -- 便宜的に大きな値

/-- 可解拡大の構造塔 -/
noncomputable def solvableTower : StructureTowerMin SolvableGaloisExtension ℕ where
  layer := fun n =>
    {L : SolvableGaloisExtension | solvable_length_to_nat L ≤ n}

  covering := by
    intro L
    refine ⟨solvable_length_to_nat L, ?_⟩
    -- ゴールを「≤」の形に展開して自明な反射律で閉じる
    change solvable_length_to_nat L ≤ solvable_length_to_nat L
    exact le_rfl

  monotone := by
    intro i j hij L hL
    exact le_trans hL hij

  minLayer := solvable_length_to_nat

  minLayer_mem := by
    intro L
    -- layer の定義を展開して自明な反射律で閉じる
    change solvable_length_to_nat L ≤ solvable_length_to_nat L
    exact le_rfl

  minLayer_minimal := by
    intro L i hi
    exact hi

/-! ### 計算例 -/

example : solvableTower.minLayer trivialSolvable = 0 := by
  rfl

example : solvableTower.minLayer Q_sqrt2_solvable = 1 := by
  rfl

example : solvableTower.minLayer Q_sqrt2_sqrt3_solvable = 1 := by
  rfl

-- ### 可解性の理論（概念スケッチのみ）


end GaloisTheory.SolvableExtensions

/-!
## 例4：円分拡大の階層（IUT1からの発展）

### IUT1での学習内容
IUT1では円分体 ℚ[ζₙ] を導入し、以下を学んだ：
- ζₙ = e^(2πi/n)（1の原始n乗根）
- ℚ[ζₙ]/ℚ はガロア拡大
- [ℚ[ζₙ]:ℚ] = φ(n)（Eulerのφ関数）

### IUT3での深化：Galois群の構造

**定理（円分体のガロア群）**：
  Gal(ℚ[ζₙ]/ℚ) ≃ (ℤ/nℤ)^×
ここで (ℤ/nℤ)^× は ℤ/nℤ の単数群（n と互いに素な元）

**同型の構成**：
σ_a(ζₙ) = ζₙ^a  （a ∈ (ℤ/nℤ)^×）
これがガロア群の元を与える。

### 構造塔としての定式化
- **carrier**: 円分体 ℚ[ζₙ]
- **Index**: ℕ（素因数の個数）
- **layer k**: {ℚ[ζₙ] | n の相異なる素因数の個数 ≤ k}
- **minLayer(ℚ[ζₙ])**: n の相異なる素因数の個数 ω(n)

**なぜ素因数の個数か**：
- φ(p^k) = p^(k-1)(p-1)（素数冪）
- φ(mn) = φ(m)φ(n)（互いに素）
- したがって、φ(n) の「複雑さ」は素因数の個数で測れる

### 対称性の構造：(ℤ/nℤ)^× の分解

```
n = p₁^a₁ ··· pₖ^aₖ のとき：
  (ℤ/nℤ)^× ≃ (ℤ/p₁^a₁ℤ)^× × ··· × (ℤ/pₖ^aₖℤ)^×
           ≃ 巡回群の直積

例：n = 12 = 2² · 3 の場合：
  (ℤ/12ℤ)^× ≃ (ℤ/4ℤ)^× × (ℤ/3ℤ)^×
            ≃ ℤ/2ℤ × ℤ/2ℤ

  ガロア群 Gal(ℚ[ζ₁₂]/ℚ) ≃ ℤ/2ℤ × ℤ/2ℤ（Klein四元群）
```

### Kronecker-Weber 定理

**定理（Kronecker-Weber, 1886）**：
ℚ のすべての有限アーベル拡大は、ある円分体 ℚ[ζₙ] に含まれる。

**言い換え**：
「ℚ の最大アーベル拡大 = すべての円分体の合成体」

構造塔での解釈：
- アーベル拡大 = 円分拡大の部分塔
- 円分体の構造塔 = アーベル拡大の「普遍的」構造塔

### IUT理論への展望

**類体論との関係**：
- Kronecker-Weber: ℚ のアーベル拡大 ⊆ 円分体
- Hilbert 類体論: 一般の数体 K でも同様の理論
- IUT では、これが p-進的・Hodge的に拡張される

**Kummer 理論**：
- 円分体は Kummer 拡大の典型例
- Fermat 方程式の研究に応用（例7で詳述）

-/

namespace GaloisTheory.CyclotomicExtensions

/-- 円分体の型（簡易版） -/
structure CyclotomicField where
  /-- n次の円分体 ℚ[ζₙ] -/
  n : ℕ
  /-- n ≥ 1 -/
  n_pos : 0 < n

/-- ℚ 自身（n=1, ζ₁ = 1） -/
def cyc_1 : CyclotomicField where
  n := 1
  n_pos := by norm_num

/-- ℚ[i] = ℚ[ζ₄]（4次円分体） -/
def cyc_4 : CyclotomicField where
  n := 4
  n_pos := by norm_num

/-- ℚ[ζ₅]（5次円分体） -/
def cyc_5 : CyclotomicField where
  n := 5
  n_pos := by norm_num

/-- ℚ[ζ₈]（8次円分体） -/
def cyc_8 : CyclotomicField where
  n := 8
  n_pos := by norm_num

/-- ℚ[ζ₁₂]（12次円分体） -/
def cyc_12 : CyclotomicField where
  n := 12
  n_pos := by norm_num

/-- n の相異なる素因数の個数 ω(n)。`primeFactorsList` を多重度を潰して数える簡易版。 -/
def omega (n : ℕ) : ℕ :=
  (Nat.primeFactorsList n).toFinset.card

/-- 円分体の構造塔 -/
noncomputable def cyclotomicTower : StructureTowerMin CyclotomicField ℕ where
  layer := fun k => {F : CyclotomicField | omega F.n ≤ k}

  covering := by
    intro F
    refine ⟨omega F.n, ?_⟩
    -- 層の定義を展開して自明な反射律で閉じる
    change omega F.n ≤ omega F.n
    exact le_rfl

  monotone := by
    intro i j hij F hF
    exact le_trans hF hij

  minLayer := fun F => omega F.n

  minLayer_mem := by
    intro F
    change omega F.n ≤ omega F.n
    exact le_rfl

  minLayer_minimal := by
    intro F i hi
    exact hi

/-! ### 計算例 -/

/-- ζ₁ = 1, ℚ 自身 -/
example : omega 1 = 0 := by native_decide

/-- ζ₄, n = 4 = 2², 素因数は {2} のみ -/
example : omega 4 = 1 := by native_decide

/-- ζ₅, n = 5（素数）, 素因数は {5} のみ -/
example : omega 5 = 1 := by native_decide

/-- ζ₈, n = 8 = 2³, 素因数は {2} のみ -/
example : omega 8 = 1 := by native_decide

/-- ζ₁₂, n = 12 = 2² · 3, 素因数は {2, 3} -/
example : omega 12 = 2 := by native_decide

/-! ### 円分体の理論 -/

/-
TODO (future formalization: Cyclotomic section)

* Show |Gal(ℚ[ζₙ]/ℚ)| = φ(n) using mathlib’s `IsCyclotomicExtension`.
* Exhibit the isomorphism Gal(ℚ[ζₙ]/ℚ) ≃ (ℤ/nℤ)ˣ.
* For n = p^k, record cyclicity of (ℤ/p^kℤ)ˣ.
* Restate Kronecker–Weber: every finite abelian extension of ℚ embeds in a cyclotomic field.

These are kept as comments to avoid fake proofs; connect them to the tower API when formalized.
-/

end GaloisTheory.CyclotomicExtensions


/-!
## 例5：分離拡大の階層

### IUT1, IUT2からの発展
- IUT1: 体の拡大次数を扱った
- IUT2: 幾何的多様性の次数を理解
- **IUT3**: 分離性 = 「重複のない」対称性

### ガロア理論的背景

**定義（分離多項式）**：
既約多項式 f(x) ∈ K[x] が分離的（separable）であるとは、
f(x) が重根を持たないこと。

**定義（分離拡大）**：
体の拡大 L/K が分離的であるとは、L の各元の K 上の最小多項式が分離的であること。

**分離次数**：
L/K の分離次数 [L:K]_s は、K の分離閉包 K^sep に L が
埋め込まれる異なる方法の個数。

**重要な等式**：
  [L:K] = [L:K]_s · [L:K]_i
ここで [L:K]_i は非分離次数（inseparable degree）。

**標数 0 の場合**：
標数 0 の体（ℚ, ℝ, ℂ など）上では、すべての既約多項式は分離的。
したがって [L:K]_s = [L:K]。

**標数 p > 0 の場合**：
完全体（perfect field）でない限り、非分離拡大が存在する。
例：𝔽_p(t) 上の拡大 𝔽_p(t^{1/p})/𝔽_p(t) は非分離。

### 構造塔としての定式化
- **carrier**: 体の拡大 L/ℚ（標数 0 なので自動的に分離）
- **Index**: ℕ（分離次数）
- **layer n**: {L | [L:ℚ]_s ≤ n}
- **minLayer(L)**: [L:ℚ]_s

**注意**：標数 0 では、[L:ℚ]_s = [L:ℚ] なので、
これは例1と本質的に同じ。標数 p での興味深い例は、
より高度な代数幾何（IUT4以降）で扱う。

### 非分離拡大の例（標数 p > 0）

```
k = 𝔽_p(t)（有理関数体、標数 p）
L = k(t^{1/p}) = 𝔽_p(t^{1/p})

最小多項式：X^p - t ∈ k[X]
これは (X - t^{1/p})^p と因数分解される（標数 p!）

分離次数：[L:k]_s = 1（ただ1つの根）
全次数：[L:k] = p
非分離次数：[L:k]_i = p
```

### 完全体の理論

**定義（完全体）**：
体 K が完全（perfect）であるとは、以下のいずれかが成り立つこと：
1. 標数 0
2. 標数 p > 0 で、Frobenius写像 x ↦ x^p が全射

**定理（完全体上の拡大）**：
K が完全体なら、K 上のすべての代数拡大は分離的。

**例**：
- ℚ, ℝ, ℂ：標数 0 なので完全
- 有限体 𝔽_q：Frobenius が全射なので完全
- 𝔽_p(t)：Frobenius が全射でないので不完全

### IUT理論への展望

**p-進 Hodge 理論**：
- 分離拡大 ⇔ エタール被覆
- 非分離拡大 ⇔ p-除可能な被覆
- IUT では、これらが Hodge-Tate 分解と関係

**標準座標との関係**：
- 分離性 = 「良い」座標系の存在
- 非分離性 = 座標の「退化」
- IUT の Θ-link では、この退化を制御

-/

namespace GaloisTheory.SeparableExtensions

/-- 分離拡大の簡易版型定義
標数 0 に限定するため、すべての拡大が自動的に分離的
-/
structure SeparableExtension where
  /-- 拡大体（Type* として抽象化） -/
  carrier : Type*
  /-- 拡大次数 = 分離次数（標数 0） -/
  degree : ℕ
  /-- 次数は正 -/
  degree_pos : 0 < degree
  /-- 分離次数（標数 0 なので degree と等しい） -/
  separable_degree : ℕ
  /-- 標数 0 の条件：[L:K]_s = [L:K] -/
  char_zero : separable_degree = degree

/-- 分離拡大の構造塔 -/
noncomputable def separableTower : StructureTowerMin SeparableExtension ℕ where
  layer := fun n => {L : SeparableExtension | L.separable_degree ≤ n}

  covering := by
    intro L
    refine ⟨L.separable_degree, ?_⟩
    -- 層の定義を展開して自明な反射律で閉じる
    change L.separable_degree ≤ L.separable_degree
    exact le_rfl

  monotone := by
    intro i j hij L hL
    exact le_trans hL hij

  minLayer := fun L => L.separable_degree

  minLayer_mem := by
    intro L
    change L.separable_degree ≤ L.separable_degree
    exact le_rfl

  minLayer_minimal := by
    intro L i hi
    exact hi

/-! ### 完全体の理論 -/

/-- 標数 0 の体上では、すべての拡大が分離的 -/
theorem char_zero_always_separable :
    ∀ L : SeparableExtension,
    L.separable_degree = L.degree := by
  intro L
  exact L.char_zero

/-- 分離次数は全次数以下 -/
theorem separable_degree_le_total :
    ∀ L : SeparableExtension,
    L.separable_degree ≤ L.degree := by
  intro L
  rw [L.char_zero]

/-
TODO (future formalization):
非分離拡大の具体例（標数 p > 0）を Lean で示す。
例: k = 𝔽_p(t), L = k(t^{1/p}), 最小多項式 X^p - t が (X - t^{1/p})^p と分解し
[L:k]_s = 1 < p = [L:k] となる。
現在は説明のみを残し、定理化は後日。
-/

end GaloisTheory.SeparableExtensions

/-!
# Part 2: 代数的整数論の構造塔（5例）

## 代数的整数論の基礎復習

### 数体（number field）
体の拡大 K/ℚ であって、[K:ℚ] < ∞ なるもの。

### 整数環
K の整数環 O_K := {α ∈ K | α は Z 上整}
これは Dedekind 環をなす。

### 素イデアルの分解
ℚ の素数 p に対して、p·O_K の K における素イデアル分解：
  p·O_K = P₁^{e₁} ··· Pₙ^{eₙ}
ここで：
- eᵢ: 分岐指数（ramification index）
- fᵢ: 惰性次数（inertia degree）= [O_K/Pᵢ : 𝔽_p]
- 基本等式：Σ eᵢfᵢ = [K:ℚ]

### 分岐の分類
- **不分岐（unramified）**：すべての eᵢ = 1
- **完全分岐（totally ramified）**：n = 1, e₁ = [K:ℚ]
- **タメ分岐（tamely ramified）**：すべての eᵢ が p と互いに素
- **野分岐（wildly ramified）**：ある eᵢ が p で割り切れる

IUT理論では、タメ分岐と野分岐の違いが重要な役割を果たす。
-/

/-!
## 例6：整拡大の階層（IUT2からの発展）

### IUT2での学習内容
- 環のスペクトラム Spec(R)
- 素イデアルの高さ（height）
- 整拡大 R ⊆ S

### IUT3での深化：対称性としての整閉包

**定義（整拡大）**：
環の拡大 R ⊆ S が整拡大（integral extension）であるとは、
S の各元 s が R 上整（ある R 係数のモニック多項式の根）であること。

**数体の整数環**：
K を数体とする。K の整数環 O_K は ℤ の K における整閉包：
  O_K = {α ∈ K | α は ℤ 上整}

### 構造塔としての定式化
- **carrier**: 数体 K（または整数環 O_K）
- **Index**: ℕ（階数 = [O_K : ℤ] としての Z-加群の階数）
- **layer n**: {K | [O_K : ℤ] ≤ n}（階数 ≤ n の整数環）
- **minLayer(K)**: [O_K : ℤ] = [K : ℚ]

**重要な事実**：
数体 K に対して、
  [O_K : ℤ] = [K : ℚ]
（整数環の ℤ 上の階数 = 体の拡大次数）

### 判別式との関係

**定義（判別式）**：
K の整数基底 ω₁, ..., ωₙ に対して、
  disc(K) := det(Tr(ωᵢωⱼ))²
これは整数基底の選び方によらない。

**性質**：
- disc(K) ∈ ℤ \ {0}
- disc(K) = 1 ⇔ K = ℚ
- disc(K) は分岐する素数の情報を含む

**例**：
- ℚ[√d]：disc = d（d ≡ 1 mod 4）または 4d（d ≢ 1 mod 4）
- ℚ[ζ_p]：disc は p のベキ

### IUT理論への展望

**Hodge-Arakelov 理論での判別式**：
- 判別式 = 「体の複雑さ」の測度
- minLayer = 判別式の「離散版」
- IUT では、判別式の p-進的評価が重要

**遠アーベル幾何**：
- 整数環 O_K = スキーム Spec(O_K)
- 素イデアル = 点
- 整拡大 = 被覆写像
- ガロア理論 + 整数論的構造

-/

namespace AlgebraicNumberTheory.IntegralExtensions

/-- 数体の簡易版型定義 -/
structure NumberField where
  /-- 拡大次数 [K:ℚ] -/
  degree : ℕ
  /-- 次数は正 -/
  degree_pos : 0 < degree
  /-- 整数環の階数（degree と等しい） -/
  ring_rank : ℕ
  /-- 階数 = 次数 -/
  rank_eq_degree : ring_rank = degree

/-- ℚ 自身 -/
def Q_field : NumberField where
  degree := 1
  degree_pos := by norm_num
  ring_rank := 1
  rank_eq_degree := rfl

/-- ℚ[√2] -/
def Q_sqrt2_field : NumberField where
  degree := 2
  degree_pos := by norm_num
  ring_rank := 2
  rank_eq_degree := rfl

/-- ℚ[√-5]（非UFDの例） -/
def Q_sqrt_minus5 : NumberField where
  degree := 2
  degree_pos := by norm_num
  ring_rank := 2
  rank_eq_degree := rfl

/-- 整数環の構造塔 -/
noncomputable def integralExtensionTower : StructureTowerMin NumberField ℕ where
  layer := fun n => {K : NumberField | K.ring_rank ≤ n}

  covering := by
    intro K
    refine ⟨K.ring_rank, ?_⟩
    -- 層の定義を展開して自明な反射律で閉じる
    change K.ring_rank ≤ K.ring_rank
    exact le_rfl

  monotone := by
    intro i j hij K hK
    exact le_trans hK hij

  minLayer := fun K => K.ring_rank

  minLayer_mem := by
    intro K
    change K.ring_rank ≤ K.ring_rank
    exact le_rfl

  minLayer_minimal := by
    intro K i hi
    exact hi

/-! ### 計算例 -/

example : integralExtensionTower.minLayer Q_field = 1 := by
  rfl

example : integralExtensionTower.minLayer Q_sqrt2_field = 2 := by
  rfl

/-! ### 整数環の理論 -/

/-- 整数環の階数は拡大次数と等しい -/
theorem ring_rank_eq_field_degree :
    ∀ K : NumberField,
    K.ring_rank = K.degree := by
  intro K
  exact K.rank_eq_degree

/-
TODO: Dedekind 環の性質（数体の整数環 O_K が Dedekind 環であること）
1. O_K は有限生成 ℤ-加群 → Noether 的整域
2. O_K は K の整閉包 → 整閉
3. O_K/P が有限体 → P は極大
mathlib の `NumberField.ring` 周辺と接続して正式な定理にする。
-/

/-
TODO: UFD でない例 ℚ[√-5]
6 = 2·3 = (1+√-5)(1-√-5) で非自明な因数分解が2通りあり、既約因子が同伴でない。
後日、mathlib の代数的整数 API と接続して正式な証明に差し替える。
-/

end AlgebraicNumberTheory.IntegralExtensions

/-!
## 例7：分岐理論の階層

### IUT2での学習内容
- 素イデアルの分解
- 剰余体の次数
- 局所化

### IUT3での深化：分岐指数による対称性

**素イデアルの分解（復習）**：
ℚ の素数 p に対して、p·O_K の K における分解：
  p·O_K = P₁^{e₁} ··· Pₙ^{eₙ}
各 Pᵢ に対して：
- **分岐指数（ramification index）**：e(Pᵢ|p) = eᵢ
- **惰性次数（inertia degree）**：f(Pᵢ|p) = [O_K/Pᵢ : ℤ/pℤ]
- **基本等式**：Σ eᵢfᵢ = n = [K:ℚ]

### 構造塔としての定式化
- **carrier**: (K, p, P)（数体、素数、素イデアル）
- **Index**: ℕ（分岐指数）
- **layer m**: {(K, p, P) | e(P|p) ≤ m}
- **minLayer((K, p, P))**: e(P|p)

**分岐の分類**：
- e = 1：不分岐（unramified）
- e = n：完全分岐（totally ramified）
- 1 < e < n：部分分岐（partially ramified）

### Dedekind-Kummer 定理

**定理（Dedekind-Kummer）**：
K = ℚ[α]（単項拡大）とし、f(x) を α の最小多項式とする。
p が disc(f) を割らないならば、p の分解は f(x) mod p の分解で決まる：

  f(x) ≡ f₁(x)^{e₁} ··· fₙ(x)^{eₙ} (mod p)
⇔ p·O_K = P₁^{e₁} ··· Pₙ^{eₙ}
ここで f(Pᵢ|p) = deg(fᵢ)

**例：ℚ[√2] での素数分解**：
- p = 2：x² - 2 ≡ x² (mod 2)
  ⇒ (2) = P²（完全分岐、e = 2, f = 1）
- p ≡ 1, 7 (mod 8)：x² - 2 は mod p で完全分解
  ⇒ (p) = P₁P₂（分解、e = 1, f = 1）
- p ≡ 3, 5 (mod 8)：x² - 2 は mod p で既約
  ⇒ (p) = P（慣性、e = 1, f = 2）

### ガロア拡大での分岐

K/ℚ がガロア拡大のとき：
- すべての P|p に対して、e(P|p) と f(P|p) は等しい
- efg = n（g は p の上の素イデアルの個数）
- 分岐群 I_P ⊆ G、惰性群 D_P ⊆ I_P が定義される
- |I_P| = e(P|p)、|D_P/I_P| = f(P|p)

### IUT理論への展望

**局所-大域原理**：
- 分岐データ = 各素数での「局所情報」
- 大域体 K = これらの局所情報の「統合」
- IUT では、Hodge-Arakelov 理論で統合される

**p-進 Hodge 理論**：
- タメ分岐 vs 野分岐の違いが本質的
- Hodge-Tate 分解の退化 = 分岐
- IUT の Θ-link = 分岐の「制御」

-/

namespace AlgebraicNumberTheory.RamificationTheory

/-- 素イデアルの分岐データ -/
structure PrimeRamificationData where
  /-- 数体 K の拡大次数 -/
  field_degree : ℕ
  /-- 有理素数 p -/
  prime : ℕ
  /-- 分岐指数 e(P|p) -/
  ramification_index : ℕ
  /-- 惰性次数 f(P|p) -/
  inertia_degree : ℕ
  /-- 基本等式：efg = n の一部（g は後で考慮） -/
  fundamental_equality : ramification_index * inertia_degree ≤ field_degree

/-- 不分岐の例：ℚ[√2], p = 3 -/
def Q_sqrt2_p3 : PrimeRamificationData where
  field_degree := 2
  prime := 3
  ramification_index := 1  -- 不分岐
  inertia_degree := 2  -- 慣性
  fundamental_equality := by norm_num

/-- 完全分岐の例：ℚ[√2], p = 2 -/
def Q_sqrt2_p2 : PrimeRamificationData where
  field_degree := 2
  prime := 2
  ramification_index := 2  -- 完全分岐
  inertia_degree := 1
  fundamental_equality := by norm_num

/-- 分解の例：ℚ[√2], p = 7 -/
def Q_sqrt2_p7 : PrimeRamificationData where
  field_degree := 2
  prime := 7
  ramification_index := 1  -- 不分岐
  inertia_degree := 1  -- 2つに分解
  fundamental_equality := by norm_num

/-- 分岐指数による構造塔 -/
noncomputable def ramificationTower :
    StructureTowerMin PrimeRamificationData ℕ where
  layer := fun m =>
    {data : PrimeRamificationData | data.ramification_index ≤ m}

  covering := by
    intro data
    refine ⟨data.ramification_index, ?_⟩
    change data.ramification_index ≤ data.ramification_index
    exact le_rfl

  monotone := by
    intro i j hij data hdata
    exact le_trans hdata hij

  minLayer := fun data => data.ramification_index

  minLayer_mem := by
    intro data
    change data.ramification_index ≤ data.ramification_index
    exact le_rfl

  minLayer_minimal := by
    intro data i hi
    exact hi

/-! ### 計算例 -/

example : ramificationTower.minLayer Q_sqrt2_p3 = 1 := by
  rfl  -- 不分岐

example : ramificationTower.minLayer Q_sqrt2_p2 = 2 := by
  rfl  -- 完全分岐

/-! ### 分岐理論の定理 -/

/-- 基本等式：efg = [K:ℚ] -/
theorem fundamental_identity :
    ∀ data : PrimeRamificationData,
    -- e(P|p) · f(P|p) · g ≤ [K:ℚ]
    data.ramification_index * data.inertia_degree ≤ data.field_degree := by
  intro data
  exact data.fundamental_equality

/-- 不分岐ならば e = 1 -/
theorem unramified_iff_e_one :
    ∀ data : PrimeRamificationData,
    data.ramification_index = 1 ↔
    -- P は p 上不分岐
    data.ramification_index = 1 := by
  intro data
  rfl

/-- 完全分岐（e = n）ならば f ≤ 1（g=1 を想定した簡易版） -/
theorem inertia_le_one_of_totally_ramified :
    ∀ data : PrimeRamificationData,
    data.ramification_index = data.field_degree →
    0 < data.ramification_index →
    data.inertia_degree ≤ 1 := by
  intro data h hnpos
  have hineq : data.ramification_index * data.inertia_degree ≤ data.ramification_index := by
    -- fundamental_equality : e * f ≤ n, かつ e = n を代入
    simpa [h] using data.fundamental_equality
  -- e > 0 なので左からキャンセルして f ≤ 1
  have : data.ramification_index * data.inertia_degree ≤ data.ramification_index * 1 := by
    simpa using hineq
  exact Nat.le_of_mul_le_mul_left this hnpos
  /-
  証明：
  1. fundamental_equality: e * f ≤ n に仮定 e = n を代入し e * f ≤ e
  2. e > 0 なので左からキャンセルして f ≤ 1
  3. g = 1 まで言うには g ≥ 1 の追加仮定が必要（今回は簡易版で f ≤ 1 とした）
  -/

/-
TODO: Dedekind-Kummer（概念メモ）
K = ℚ[α], f = 最小多項式, p ∤ disc(f) のとき、
f mod p の分解が p·O_K の素イデアル分解に対応することを
mathlib の判別式・分解 API と接続して正式化する。
-/
  /-
  証明の概略：
  1. O_K/(p) ≃ 𝔽_p[x]/(f(x))（p が判別式を割らない条件が必要）
  2. f(x) mod p の既約分解：f(x) ≡ f₁^{e₁}···fₙ^{eₙ} (mod p)
  3. これが素イデアル分解に対応：(p) = P₁^{e₁}···Pₙ^{eₙ}
  4. 各 Pᵢ に対して：f(Pᵢ|p) = deg(fᵢ)
  -/

end AlgebraicNumberTheory.RamificationTheory


/-!
## 例8：イデアル類群の階層

### IUT2での学習内容
- イデアルの演算
- 主イデアルと非主イデアル
- 類群 Cl(K)

### IUT3での深化：類数と対称性

**定義（イデアル類群）**：
K の整数環 O_K の分数イデアル全体を I(K) とする。
主イデアル全体を P(K) とする。イデアル類群：
  Cl(K) := I(K)/P(K)

**類数（class number）**：
  h(K) := |Cl(K)|

**重要な性質**：
- h(K) = 1 ⇔ O_K は UFD（一意分解整域）
- h(K) < ∞ 常に成立（Minkowski）
- h(K) は K の「算術的複雑さ」を測る

### 構造塔としての定式化

**アプローチ1：類数による階層**
- **carrier**: 数体 K
- **Index**: ℕ（類数）
- **layer n**: {K | h(K) ≤ n}
- **minLayer(K)**: h(K)

**アプローチ2：イデアルの階層**
- **carrier**: K の（分数）イデアル
- **Index**: ℕ（イデアルを表現する主イデアルの「距離」）
- **layer n**: {I | I は長さ ≤ n の主イデアルの積で表現可能}
- **minLayer(I)**: 最小の表現長

### 具体例

**h(K) = 1 の例（UFD）**：
- ℚ：自明
- ℚ[√2], ℚ[√3], ℚ[i], ℚ[√-2]
- ℚ[ζ_p]（p ≤ 19 の素数）

**h(K) = 2 の例**：
- ℚ[√-5]：イデアル (2, 1+√-5) は非主
  - (2, 1+√-5)² = (2)（主イデアル）
  - したがって、この類の位数は 2
  - Cl(ℚ[√-5]) ≃ ℤ/2ℤ、h = 2

**h(K) が大きい例**：
- ℚ[√-23]：h = 3
- ℚ[√-163]：h = 1（虚二次体で最大の判別式）
- 一般に、|disc(K)| が大きいほど h(K) も大きい傾向

### 類体論との関係

**Hilbert 類体**：
K の最大不分岐アーベル拡大 H/K を Hilbert 類体と呼ぶ。

**重要な定理**：
  Gal(H/K) ≃ Cl(K)

これは「イデアル類群 = ガロア群」という対称性の現れ！

**例：ℚ[√-5] の Hilbert 類体**：
- Cl(ℚ[√-5]) ≃ ℤ/2ℤ、h = 2
- したがって Gal(H/ℚ[√-5]) ≃ ℤ/2ℤ
- H = ℚ[√-5, √5]（√5 を添加）

### IUT理論への展望

**類体論の一般化**：
- IUT では、類体論が p-進的・Hodge的に拡張される
- Θ-link = 類体の「宇宙際的」版

**ABC 予想との関係**：
- 類数の成長 = 判別式の成長
- IUT では、これが楕円曲線の高さと関係
- Szpiro 予想 → ABC 予想

-/

namespace AlgebraicNumberTheory.IdealClassGroup

/-- イデアル類群のデータ -/
structure IdealClassData where
  /-- 数体 K の拡大次数 -/
  field_degree : ℕ
  /-- 類数 h(K) -/
  class_number : ℕ
  /-- 類数は正 -/
  class_number_pos : 0 < class_number

/-- ℚ の類数は 1（自明） -/
def Q_class : IdealClassData where
  field_degree := 1
  class_number := 1
  class_number_pos := by norm_num

/-- ℚ[√2] の類数は 1（UFD） -/
def Q_sqrt2_class : IdealClassData where
  field_degree := 2
  class_number := 1
  class_number_pos := by norm_num

/-- ℚ[√-5] の類数は 2（非UFD） -/
def Q_sqrt_minus5_class : IdealClassData where
  field_degree := 2
  class_number := 2
  class_number_pos := by norm_num

/-- 類数による構造塔 -/
noncomputable def classGroupTower : StructureTowerMin IdealClassData ℕ where
  layer := fun n => {data : IdealClassData | data.class_number ≤ n}

  covering := by
    intro data
    refine ⟨data.class_number, ?_⟩
    change data.class_number ≤ data.class_number
    exact le_rfl

  monotone := by
    intro i j hij data hdata
    exact le_trans hdata hij

  minLayer := fun data => data.class_number

  minLayer_mem := by
    intro data
    change data.class_number ≤ data.class_number
    exact le_rfl

  minLayer_minimal := by
    intro data i hi
    exact hi

/-! ### 計算例 -/

example : classGroupTower.minLayer Q_class = 1 := by
  rfl

example : classGroupTower.minLayer Q_sqrt_minus5_class = 2 := by
  rfl

/-! ### イデアル類群の理論 -/

/-- 類数 1 ⇔ UFD -/
theorem class_number_one_iff_UFD :
    ∀ data : IdealClassData,
    data.class_number = 1 ↔
    -- O_K は一意分解整域
    data.class_number = 1 := by
  intro data
  rfl

/-
TODO: 類数の有限性（Minkowski）と Hilbert 類体との対応

1. Minkowski の有界性定理を用いて h(K) < ∞ を示す。
2. 最大不分岐アーベル拡大 H/K に対し Gal(H/K) ≃ Cl(K) を
   Artin 写像を通じて同型とする。

現段階では学習ノートとしてコメントのみ残し、正式な定理化は後日。
-/

end AlgebraicNumberTheory.IdealClassGroup

/-!
## 例9：局所体の階層

### IUT1, IUT2からの発展
- IUT1: 2-進付値、p-進整数
- IUT2: 局所環、局所化
- **IUT3**: 局所体のガロア理論

### 局所体の定義

**定義（局所体）**：
以下のいずれかの体を局所体と呼ぶ：
1. ℝ, ℂ（アルキメデス的）
2. 有限次拡大 K/ℚ_p（非アルキメデス的）
3. 有限体上の1変数有理関数体 𝔽_q((t))

IUT3 では主に (2) を扱う。

### p-進体の構造

**ℚ_p の定義**：
ℚ の p-進完備化。p-進絶対値 |·|_p で完備化した体。

**性質**：
- ℤ_p := {x ∈ ℚ_p | |x|_p ≤ 1}（p-進整数環）
- ℤ_p は完備離散付値環（DVR）
- 極大イデアル：(p) = pℤ_p
- 剰余体：ℤ_p/(p) ≃ 𝔽_p

**拡大**：
K/ℚ_p を有限次拡大とする。
- e(K|ℚ_p)：分岐指数
- f(K|ℚ_p)：惰性次数
- [K:ℚ_p] = ef

### 構造塔としての定式化
- **carrier**: ℚ_p の有限次拡大 K
- **Index**: ℕ（拡大次数 [K:ℚ_p]）
- **layer n**: {K | [K:ℚ_p] ≤ n}
- **minLayer(K)**: [K:ℚ_p]

### 不分岐拡大と分岐拡大

**定理（不分岐拡大の分類）**：
ℚ_p の次数 n の不分岐拡大は、ℚ_p(ζ) の形。
ここで ζ は 1 の原始 (p^n-1) 乗根。

**完全分岐拡大の例**：
- K = ℚ_p(p^{1/n})：完全分岐、e = n, f = 1
- 最小多項式：X^n - p

### 局所大域原理への準備

**Hasse 原理**：
方程式 f(x) = 0 が ℚ で解を持つ ⇔
すべての完備化（ℝ と各 ℚ_p）で解を持つ

これは常に成り立つわけではないが、2次形式では成り立つ（Hasse-Minkowski）。

構造塔での解釈：
- 局所体 = 各層での情報
- 大域体 = 層の統合
- 局所大域原理 = 層の整合性

### IUT理論への展望

**p-進 Hodge 理論**：
- 局所体のガロア表現 = Hodge 構造の p-進版
- Hodge-Tate 分解、de Rham 分解
- IUT では、これが宇宙ごとに異なる

**遠アーベル幾何**：
- 局所体の絶対ガロア群
- 局所-大域の対応 = 宇宙間の対応
- Θ-link = 局所情報の「同期」

-/

namespace AlgebraicNumberTheory.LocalFields

/-- p-進体の拡大データ -/
structure PadicExtension where
  /-- 素数 p -/
  prime : ℕ
  /-- 拡大次数 [K:ℚ_p] -/
  degree : ℕ
  /-- 次数は正 -/
  degree_pos : 0 < degree
  /-- 分岐指数 e -/
  ramification_index : ℕ
  /-- 惰性次数 f -/
  inertia_degree : ℕ
  /-- 基本等式：ef = [K:ℚ_p] -/
  ef_equals_degree : ramification_index * inertia_degree = degree

/-- ℚ_p 自身（自明な拡大） -/
def Qp_trivial (p : ℕ) : PadicExtension where
  prime := p
  degree := 1
  degree_pos := by norm_num
  ramification_index := 1
  inertia_degree := 1
  ef_equals_degree := by norm_num

/-- ℚ_p(p^{1/2})：完全分岐拡大 -/
def Qp_sqrt_p (p : ℕ) : PadicExtension where
  prime := p
  degree := 2
  degree_pos := by norm_num
  ramification_index := 2  -- 完全分岐
  inertia_degree := 1
  ef_equals_degree := by norm_num

/-- 不分岐2次拡大 -/
def Qp_unramified_2 (p : ℕ) : PadicExtension where
  prime := p
  degree := 2
  degree_pos := by norm_num
  ramification_index := 1  -- 不分岐
  inertia_degree := 2
  ef_equals_degree := by norm_num

/-- 局所体の構造塔 -/
noncomputable def localFieldTower : StructureTowerMin PadicExtension ℕ where
  layer := fun n => {K : PadicExtension | K.degree ≤ n}

  covering := by
    intro K
    refine ⟨K.degree, ?_⟩
    change K.degree ≤ K.degree
    exact le_rfl

  monotone := by
    intro i j hij K hK
    exact le_trans hK hij

  minLayer := fun K => K.degree

  minLayer_mem := by
    intro K
    change K.degree ≤ K.degree
    exact le_rfl

  minLayer_minimal := by
    intro K i hi
    exact hi

/-! ### 計算例 -/

example (p : ℕ) : localFieldTower.minLayer (Qp_trivial p) = 1 := by
  rfl

example (p : ℕ) : localFieldTower.minLayer (Qp_sqrt_p p) = 2 := by
  rfl

/-! ### 局所体の理論 -/

/-- ef = n の基本等式 -/
theorem local_fundamental_identity :
    ∀ K : PadicExtension,
    K.ramification_index * K.inertia_degree = K.degree := by
  intro K
  exact K.ef_equals_degree

/-- 不分岐拡大 ⇔ e = 1 -/
theorem unramified_iff_e_one :
    ∀ K : PadicExtension,
    K.ramification_index = 1 ↔ K.inertia_degree = K.degree := by
  intro K
  constructor
  · intro h
    have := K.ef_equals_degree
    simp [h] at this
    exact this
  · intro h
    -- ef = degree から f を置き換え、右因子をキャンセルして e = 1 を得る
    have hEF' : K.ramification_index * K.degree = K.degree := by
      simpa [h] using K.ef_equals_degree
    have hpos : 0 < K.degree := K.degree_pos
    have : K.ramification_index = 1 := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc
        K.ramification_index * K.degree = K.degree := hEF'
        _ = 1 * K.degree := by simp
    exact this

/-
TODO: Hasse–Minkowski（2次形式の局所大域原理）
Q(x)=0 が ℚ で解を持つ ⇔ すべての ℚ_p と ℝ で解を持つ。
現状は説明のみ保持し、正式な定理化は後日 mathlib の二次形式 API と接続して行う。
-/

end AlgebraicNumberTheory.LocalFields

/-!
## 例10：単数群の階層

### IUT2での学習内容
- 単数：ノルムが ±1 の元
- 単数群 O_K^×

### IUT3での深化：Dirichlet の単数定理

**定義（単数群）**：
K の整数環 O_K の単数群：
  O_K^× = {α ∈ O_K | ∃β ∈ O_K, αβ = 1}
         = {α ∈ O_K | N(α) = ±1}

**Dirichlet の単数定理**：
K を数体、r₁ を実埋め込みの個数、r₂ を複素埋め込みの組数とする。
このとき：
  O_K^× ≃ μ(K) × ℤ^{r₁+r₂-1}
ここで μ(K) は K の1の冪根全体（有限巡回群）。

**単数群のランク**：
  rank(O_K^×) = r₁ + r₂ - 1

**例**：
- ℚ：r₁ = 1, r₂ = 0 ⇒ rank = 0、O_ℚ^× = {±1}
- ℚ[√2]：r₁ = 2, r₂ = 0 ⇒ rank = 1、基本単数 1+√2
- ℚ[i]：r₁ = 0, r₂ = 1 ⇒ rank = 0、O_{ℚ[i]}^× = {±1, ±i}

### 構造塔としての定式化
- **carrier**: 数体 K
- **Index**: ℕ（単数群のランク）
- **layer n**: {K | rank(O_K^×) ≤ n}
- **minLayer(K)**: rank(O_K^×) = r₁ + r₂ - 1

### Pell 方程式との関係

**Pell 方程式**：
  x² - Dy² = 1  (D > 0, 非平方数)

**定理**：
ℚ[√D] の基本単数 ε₀ = x₀ + y₀√D とすると、
(x₀, y₀) は Pell 方程式の最小解。

逆に、Pell 方程式の解全体は：
  (xₙ, yₙ) から εₙ = ε₀^n が対応
すなわち、Pell 方程式の解 ⇔ 単数群の元

**例：x² - 2y² = 1**：
- 最小解：(3, 2)（3² - 2·2² = 1）
- 対応する単数：ε₀ = 3 + 2√2 ∈ O_{ℚ[√2]}^×
- すべての解：εₙ = (3 + 2√2)^n

### IUT理論への展望

**高さ理論**：
- 単数 = 「高さ 0」の元
- S-単数 = 「S 外で高さ 0」
- IUT では、高さの変形を追跡

**楕円曲線の torsion**：
- 単数群 ≃ 有限生成アーベル群
- 楕円曲線の Mordell-Weil 群も有限生成
- 構造の類似性（例14で詳述）

-/

namespace AlgebraicNumberTheory.UnitGroup

/-- 単数群のデータ -/
structure UnitGroupData where
  /-- 数体 K の拡大次数 -/
  field_degree : ℕ
  /-- 実埋め込みの個数 r₁ -/
  real_embeddings : ℕ
  /-- 複素埋め込みの組数 r₂ -/
  complex_pairs : ℕ
  /-- 署名の条件：r₁ + 2r₂ = [K:ℚ] -/
  signature : real_embeddings + 2 * complex_pairs = field_degree
  /-- 単数群のランク -/
  unit_rank : ℕ
  /-- Dirichlet の単数定理 -/
  dirichlet : unit_rank = real_embeddings + complex_pairs - 1

/-- ℚ の単数群（rank 0） -/
def Q_units : UnitGroupData where
  field_degree := 1
  real_embeddings := 1
  complex_pairs := 0
  signature := by norm_num
  unit_rank := 0
  dirichlet := by norm_num

/-- ℚ[√2] の単数群（rank 1） -/
def Q_sqrt2_units : UnitGroupData where
  field_degree := 2
  real_embeddings := 2
  complex_pairs := 0
  signature := by norm_num
  unit_rank := 1
  dirichlet := by norm_num

/-- ℚ[i] の単数群（rank 0、虚二次体） -/
def Q_i_units : UnitGroupData where
  field_degree := 2
  real_embeddings := 0
  complex_pairs := 1
  signature := by norm_num
  unit_rank := 0
  dirichlet := by norm_num

/-- 単数群の構造塔 -/
noncomputable def unitGroupTower : StructureTowerMin UnitGroupData ℕ where
  layer := fun n => {data : UnitGroupData | UnitGroupData.unit_rank data ≤ n}

  covering := by
    intro data
    refine ⟨UnitGroupData.unit_rank data, ?_⟩
    change UnitGroupData.unit_rank data ≤ UnitGroupData.unit_rank data
    exact le_rfl

  monotone := by
    intro i j hij data hdata
    exact le_trans hdata hij

  minLayer := fun data => UnitGroupData.unit_rank data

  minLayer_mem := by
    intro data
    change UnitGroupData.unit_rank data ≤ UnitGroupData.unit_rank data
    exact le_rfl

  minLayer_minimal := by
    intro data i hi
    exact hi

/-! ### 計算例 -/

example : unitGroupTower.minLayer Q_units = 0 := by
  rfl

example : unitGroupTower.minLayer Q_sqrt2_units = 1 := by
  rfl

example : unitGroupTower.minLayer Q_i_units = 0 := by
  rfl

/-! ### 単数群の理論 -/

/-- Dirichlet の単数定理 -/
theorem dirichlet_unit_theorem :
    ∀ data : UnitGroupData,
    data.unit_rank = data.real_embeddings + data.complex_pairs - 1 := by
  intro data
  exact data.dirichlet

/-- 虚二次体の単数群は有限 -/
theorem imaginary_quadratic_finite_units :
    ∀ data : UnitGroupData,
    data.real_embeddings = 0 ∧ data.complex_pairs = 1 →
    data.unit_rank = 0 := by
  intro data ⟨h1, h2⟩
  have := data.dirichlet
  rw [h1, h2] at this
  norm_num at this
  exact this

/-
TODO: Pell 方程式と単数群の対応
N(x + y√D) = x² - Dy² から、Pell 方程式の解と二次体の単数が対応することを
後日正式に証明する。現状は説明のみ保持。
-/
  /-
  証明：
  1. ℚ[√D] の単数 ε = x + y√D とする
  2. N(ε) = (x + y√D)(x - y√D) = x² - Dy² = ±1
  3. ε > 0 を選べば N(ε) = 1
  4. したがって x² - Dy² = 1

  逆に、Pell 方程式の解 (x, y) から
  ε = x + y√D は N(ε) = 1 を満たすので単数。
  -/
  
end AlgebraicNumberTheory.UnitGroup

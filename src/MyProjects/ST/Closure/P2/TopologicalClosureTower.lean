import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# 位相的閉包による構造塔

このファイルは、位相空間における閉包作用素を用いて構造塔を実装する。

## 数学的背景：反復閉包と導来集合

### 閉包作用素の反復

位相空間 (X, τ) において、閉包作用素 cl : 𝒫(X) → 𝒫(X) は：
- cl(A) = A の閉包（A に含まれる最小の閉集合）

この閉包を反復適用することで階層が得られる：
- cl⁰(A) = A
- cl¹(A) = cl(A)
- cl²(A) = cl(cl(A))
- cl^n(A) = cl(cl^(n-1)(A))

Cantor-Bendixson の定理により、可算な基数以下の空間では
この反復は有限段階で安定する。

### 導来集合の階層

別の視点として、導来集合（derived set）の反復も考えられる：
- A' = A の極限点の集合
- A'' = (A')' = A の第2導来集合
- A^(α) = α 次導来集合（超限帰納的に定義）

### 構造塔との対応

- **layer(n)**：n 回の閉包操作で閉じる部分集合の族
- **minLayer(x)**：点 x が初めて孤立点でなくなる段階
- **被覆性**：すべての点は有限段階で閉じる（分離公理による）
- **単調性**：閉包は単調なので n ≤ m ⇒ cl^n ⊆ cl^m

## この実装：ℚ の部分空間

基礎空間として有理数 ℚ（通常の距離位相）の有限部分集合を考える。

例：A = {1, 1/2, 1/3, 1/4, ...} ∪ {0}
- layer(0)：孤立点のみ（この例では空）
- layer(1)：A = A ∪ A' = A（既に閉集合）
- 0 は極限点なので minLayer(0) = 0
- 1/n は孤立点なので minLayer(1/n) = 0

より一般に、有限集合の閉包階層を考察する。

-/

namespace TopologicalClosureTower

/-!
## StructureTowerWithMin の定義（再掲）
-/

structure StructureTowerWithMin where
  carrier : Type
  Index : Type
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

instance (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

/-!
## 簡易版：有限集合の位相的閉包

完全な位相空間の閉包は実装が複雑なので、ここでは教育的な
簡易版を実装する。

**設定**：
- 基礎空間 X = Fin n（有限集合）
- 各点の「閉包レベル」を手動で指定
- これは一般的な閉包作用素の離散版

**具体例**：n = 5 の場合
```
点 0: 孤立点（レベル 0）
点 1: 孤立点（レベル 0）  
点 2: 1回の閉包で追加（レベル 1）
点 3: 2回の閉包で追加（レベル 2）
点 4: 極限点（レベル 0）
```

これは以下の状況をモデル化：
- 基本集合 {0, 1}
- {0, 1} の閉包に 2 が追加される
- {0, 1, 2} の閉包に 3 が追加される
- 4 は常に極限点
-/

/-- 有限空間の点 -/
def FinSpace (n : ℕ) : Type := Fin n

/-- 各点の閉包レベルを指定する関数
これは「その点が何回の閉包操作で初めて集合に含まれるか」を表す -/
def closureLevel (n : ℕ) : Fin n → ℕ := fun i => i.val % 3

/-!
## 閉包レベルの解釈

closureLevel i は以下を意味する：
- 0：その点は初めから極限点（または基本集合に含まれる）
- 1：1回の閉包操作で追加される
- 2：2回の閉包操作で必要
- 一般に k：k回の閉包操作で初めて含まれる
-/

/-- 閉包レベルに基づく構造塔 -/
noncomputable def finiteClosureTower (n : ℕ) : StructureTowerWithMin where
  carrier := FinSpace n
  Index := ℕ
  indexPreorder := inferInstance
  
  layer := fun k => {i : Fin n | closureLevel n i ≤ k}
  
  covering := by
    intro i
    use closureLevel n i
    simp
  
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij
  
  minLayer := closureLevel n
  
  minLayer_mem := by
    intro x
    simp
  
  minLayer_minimal := by
    intro x k hx
    exact hx

/-!
## 具体例：n = 5 の場合

層の構造を明示的に計算：
-/

example : (0 : Fin 5) ∈ (finiteClosureTower 5).layer 0 := by
  simp [finiteClosureTower, closureLevel]

example : (3 : Fin 5) ∈ (finiteClosureTower 5).layer 2 := by
  simp [finiteClosureTower, closureLevel]
  omega

example : (finiteClosureTower 5).minLayer (2 : Fin 5) = 2 := by
  simp [finiteClosureTower, closureLevel]

/-!
## より現実的な例：ℚ の稠密部分集合

以下は、実際の位相空間 ℚ における閉包の振る舞いを
部分的にシミュレートする例。

**数学的設定**：
- 集合 A = {1/n | n ∈ ℕ, 1 ≤ n ≤ N}
- 0 は A の極限点
- 各 1/n は孤立点（A において）

**閉包の反復**：
- cl⁰(A) = A
- cl¹(A) = A ∪ {0}
- cl²(A) = A ∪ {0}（既に閉じている）

**構造塔による記述**：
- layer(0) = A（孤立点の集合）
- layer(1) = A ∪ {0}（閉包）
- minLayer(1/n) = 0（孤立点）
- minLayer(0) = 1（極限点として追加）
-/

/-- 拡張された空間：ℚ の部分集合 + 極限点 -/
inductive ExtendedRatSpace : Type
  | rational : ℚ → ExtendedRatSpace  -- 1/n の形の有理数
  | limitPoint : ExtendedRatSpace    -- 極限点 0

/-- 極限点としての性質を判定 -/
def isLimitPoint : ExtendedRatSpace → Bool
  | .limitPoint => true
  | .rational _ => false

/-- 閉包レベル：極限点なら後で追加、そうでなければ初期 -/
def extendedClosureLevel : ExtendedRatSpace → ℕ
  | .limitPoint => 1    -- 1回の閉包で追加される極限点
  | .rational _ => 0    -- 初期の孤立点

/-- 拡張空間の構造塔 -/
noncomputable def extendedClosureTower : StructureTowerWithMin where
  carrier := ExtendedRatSpace
  Index := ℕ
  indexPreorder := inferInstance
  
  layer := fun k => {x : ExtendedRatSpace | extendedClosureLevel x ≤ k}
  
  covering := by
    intro x
    use extendedClosureLevel x
    simp
  
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij
  
  minLayer := extendedClosureLevel
  
  minLayer_mem := by
    intro x
    simp
  
  minLayer_minimal := by
    intro x k hx
    exact hx

/-!
## 具体的な計算例
-/

/-- 有理数（孤立点）は層 0 に属する -/
example : ExtendedRatSpace.rational (1/2) ∈ extendedClosureTower.layer 0 := by
  simp [extendedClosureTower, extendedClosureLevel]

/-- 極限点は層 1 に属する（0 回では閉じない） -/
example : ExtendedRatSpace.limitPoint ∈ extendedClosureTower.layer 1 := by
  simp [extendedClosureTower, extendedClosureLevel]

/-- 極限点は層 0 に属さない -/
example : ExtendedRatSpace.limitPoint ∉ extendedClosureTower.layer 0 := by
  simp [extendedClosureTower, extendedClosureLevel]
  omega

/-!
## 理論的洞察：位相的閉包と構造塔

### 1. 閉包作用素の性質

位相的閉包 cl は閉包作用素の公理を満たす：
- **単調性**：A ⊆ B ⇒ cl(A) ⊆ cl(B)
- **拡大性**：A ⊆ cl(A)
- **冪等性**：cl(cl(A)) = cl(A)

構造塔の単調性は閉包の単調性から直接従う。

### 2. minLayer の位相的意味

minLayer(x) = n は以下を意味する：
- x は n 回の閉包操作で初めて集合に含まれる
- x は (n-1) 回では集合に含まれない

特別な場合：
- minLayer(x) = 0：x は孤立点または初期集合の元
- minLayer(x) = 1：x は1次の極限点
- minLayer(x) = 2：x は2次の極限点（極限点の極限点）

### 3. Cantor-Bendixson 階数との関係

集合 A の Cantor-Bendixson 階数は、A から孤立点を
繰り返し除去して空集合になるまでの回数。

構造塔の視点では：
- 階数 0 の点 = 孤立点 = minLayer が小さい
- 階数 α の点 = α 次導来集合の点 = minLayer が大きい

### 4. 分離公理との関連

- **T₁ 空間**：一点集合が閉集合
  → すべての点の minLayer が有限

- **Perfect 空間**：孤立点がない
  → すべての点の minLayer ≥ 1

- **Scattered 空間**：完全な部分集合がない
  → 有限回の閉包で安定

### 5. 構造保存写像

位相空間の連続写像 f : X → Y は以下を満たす：
  f(cl(A)) ⊆ cl(f(A))

これは構造塔の射の layer_preserving 条件に対応。
さらに、開写像なら minLayer も保存する。

-/

/-!
## より一般的な構造：導来集合の塔

Cantor の導来集合（derived set）D(A) は A の極限点の集合。
これを反復して階層を作る：

- D⁰(A) = A
- D¹(A) = D(A)（A の極限点）
- D^(n+1)(A) = D(D^n(A))
- D^ω(A) = ⋂_{n<ω} D^n(A)（超限的な極限）

この階層は構造塔の一般化に対応：
- Index が順序数全体
- 極限順序数での層は前の層の共通部分

これは確率論のフィルトレーション理論とも対応し、
構造塔の応用範囲の広さを示している。
-/

/-!
## 学習のまとめ：位相的閉包と構造塔

### この例から学べること

1. **位相的閉包 = 閉包作用素の典型例**
   - 3つの公理（単調、拡大、冪等）を自然に満たす
   - 構造塔の単調性が直接的に成立

2. **minLayer の位相的解釈**
   - 「何回の閉包で初めて含まれるか」
   - 孤立点 vs 極限点の区別
   - Cantor-Bendixson 階数との対応

3. **位相不変量としての構造**
   - 連続写像が構造塔の射を誘導
   - 位相的性質が構造塔の性質に反映

4. **他の分野との統一的視点**
   - 線形包（代数）
   - 位相的閉包（位相）
   - フィルトレーション（確率論）
   
   これらすべてが構造塔の枠組みで統一的に扱える。

### Bourbaki の母構造思想の実現

この例は、Bourbaki の「位相構造」という母構造が
構造塔理論で自然に記述できることを示している。

順序構造（階層）と位相構造（閉包）の融合が、
構造塔という統一的な枠組みを生み出している。

-/

end TopologicalClosureTower

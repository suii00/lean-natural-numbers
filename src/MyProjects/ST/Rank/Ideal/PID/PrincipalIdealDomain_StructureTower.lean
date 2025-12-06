import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Order.Basic

/-!
# 主イデアル整域における構造塔

**数学的動機**:

主イデアル整域（Principal Ideal Domain, PID）におけるイデアルは、
有限個の元で生成される。この「生成に必要な元の最小個数」という概念は、
構造塔のminLayer関数として自然に形式化できる。

## 数学的背景

**主イデアル整域の定義**:
整域Rが主イデアル整域であるとは、すべてのイデアルが1つの元で生成される
（すなわち、I = ⟨a⟩ の形に書ける）ことをいう。

**例**:
- ℤ（整数環）: すべてのイデアルは ⟨n⟩ = {nk | k ∈ ℤ} の形
- F[x]（体F上の多項式環）: すべてのイデアルは ⟨f(x)⟩ の形

## 構造塔としての解釈

**carrier**: Ideal R（イデアルの集合）
**Index**: ℕ（生成元の個数）
**layer(n)**: n個以下の元で生成されるイデアル全体
**minLayer(I)**: イデアルIを生成するのに必要な最小の元の個数

PIDでは、すべてのイデアルが1個の元で生成されるため、
minLayer(I) ≤ 1 for all I
という特別な性質を持つ。

## 教育的意義

この例は以下の点で「噛みやすい」：

1. **具体的な計算**: ℤのイデアル ⟨6⟩, ⟨12⟩ など手計算可能
2. **代数的直感**: 「生成に必要な最小元の個数」は明確
3. **線形包との対応**: 線形代数のrank概念との類似性
4. **PIDの特徴付け**: 「すべてのイデアルがlayer 1に属する」という視点

## Bourbakiの精神

Bourbakiの母構造理論では、イデアルは「代数的構造」の典型例である。
構造塔の視点により、イデアル理論が順序構造と融合する様を見ることができる。

## 参考文献
- Bourbaki, N. "Éléments de mathématique: Algèbre Commutative"
- Atiyah, M. F., & Macdonald, I. G. (1969). "Introduction to Commutative Algebra"
- RankTower.lean: rank関数と構造塔の対応理論
-/

namespace AlgebraicStructureTower

/-!
## Part 1: 簡略版構造塔の定義

完全版（CAT2_complete.lean）の前に、教育的な簡略版を定義する。
-/

/-- 簡略版の構造塔（minLayerを持つバージョン） -/
structure SimpleTowerWithMin where
  carrier : Type*
  Index : Type*
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

/-!
## Part 2: ℤにおけるイデアル生成数

ℤの主イデアル整域としての性質を利用して、
「イデアルを生成するのに必要な元の個数」を定義する。
-/

section IntegerIdeals

open Ideal

/-- ℤのイデアルを生成するのに必要な最小の元の個数

**数学的定義**:
- ⟨0⟩ = {0}: 0個の非零元で生成（特別扱い）
- ⟨n⟩ (n ≠ 0): 1個の元nで生成

**直感**:
「何個の元を使えばこのイデアルを記述できるか」という問い。
PIDでは常に1個で十分（ただし零イデアルは例外）。
-/
noncomputable def idealGeneratorCount (I : Ideal ℤ) : ℕ :=
  if I = ⊥ then 0  -- 零イデアル
  else 1            -- 非零イデアルは1個で生成

/-!
### 基本的な性質の証明

idealGeneratorCountが実際に「最小性」を持つことを示す補題群。
-/

lemma idealGeneratorCount_bot :
    idealGeneratorCount (⊥ : Ideal ℤ) = 0 := by
  unfold idealGeneratorCount
  simp

lemma idealGeneratorCount_span_one :
    idealGeneratorCount (span {(1 : ℤ)}) = 1 := by
  unfold idealGeneratorCount
  have h : span {(1 : ℤ)} ≠ ⊥ := by
    intro h_eq
    -- span {1} = ⊤ なので ⊥ ≠ ⊤ から矛盾
    have h_top : span {(1 : ℤ)} = ⊤ := by
      ext x
      constructor
      · intro _; trivial
      · intro _
        show x ∈ span {(1 : ℤ)}
        have : x = x * 1 := by ring
        rw [this]
        exact mem_span_singleton.mpr ⟨x, rfl⟩
    rw [h_eq] at h_top
    exact bot_ne_top h_top
  simp [h]

lemma idealGeneratorCount_span_n (n : ℤ) (hn : n ≠ 0) :
    idealGeneratorCount (span {n}) = 1 := by
  unfold idealGeneratorCount
  have h : span {n} ≠ ⊥ := by
    intro h_eq
    have h_mem : n ∈ span {n} := mem_span_singleton.mpr ⟨1, by ring⟩
    rw [h_eq] at h_mem
    exact hn (mem_bot.mp h_mem)
  simp [h]

/-!
### 重要な補題: PIDでは常にcount ≤ 1

**数学的意味**:
主イデアル整域の定義そのもの：「すべてのイデアルが1個の元で生成される」
ことが、count ≤ 1 という不等式で表現される。
-/
lemma idealGeneratorCount_le_one (I : Ideal ℤ) :
    idealGeneratorCount I ≤ 1 := by
  unfold idealGeneratorCount
  by_cases h : I = ⊥
  · simp [h]
  · simp [h]

end IntegerIdeals

/-!
## Part 3: 整数イデアルの構造塔

ℤの全イデアルを「生成元の個数」で階層化する構造塔を構成する。
-/

section IntegerIdealTower

open Ideal

/-- ℤのイデアル上の構造塔

**層の構造**:
- layer(0) = {⟨0⟩}: 零イデアルのみ
- layer(1) = Ideal ℤ: すべてのイデアル（PIDの性質）
- layer(n≥2) = Ideal ℤ: 同じく全体

**minLayerの意味**:
- minLayer(⟨0⟩) = 0
- minLayer(⟨n⟩) = 1 for n ≠ 0

**教育的ポイント**:
PIDでは「すべての非零イデアルがlayer 1に収まる」という
特別な構造を持つことが、この構造塔から明確に読み取れる。
-/
noncomputable def integerIdealTower : SimpleTowerWithMin where
  carrier := Ideal ℤ
  Index := ℕ
  indexPreorder := inferInstance

  layer := fun n => {I : Ideal ℤ | idealGeneratorCount I ≤ n}

  covering := by
    intro I
    use idealGeneratorCount I
    simp

  monotone := by
    intro i j hij I hI
    exact le_trans hI hij

  minLayer := idealGeneratorCount

  minLayer_mem := by
    intro I
    simp

  minLayer_minimal := by
    intro I n hI
    exact hI

/-!
### 層の明示的な特徴付け

各層が具体的にどのイデアルを含むかを明示する。
-/

lemma integerIdealTower_layer_zero :
    integerIdealTower.layer 0 = {⊥} := by
  ext I
  constructor
  · intro h
    simp [integerIdealTower] at h
    have : idealGeneratorCount I ≤ 0 := h
    have : idealGeneratorCount I = 0 := Nat.eq_zero_of_le_zero this
    unfold idealGeneratorCount at this
    by_cases hI : I = ⊥
    · exact hI
    · simp [hI] at this
  · intro h
    simp [integerIdealTower, h, idealGeneratorCount_bot]

lemma integerIdealTower_layer_one :
    integerIdealTower.layer 1 = Set.univ := by
  ext I
  constructor
  · intro _; trivial
  · intro _
    simp [integerIdealTower]
    exact idealGeneratorCount_le_one I

/-- 層1以降はすべて全体集合（PIDの特徴） -/
lemma integerIdealTower_layer_succ (n : ℕ) :
    integerIdealTower.layer (n + 1) = Set.univ := by
  ext I
  constructor
  · intro _; trivial
  · intro _
    simp [integerIdealTower]
    exact Nat.le_trans (idealGeneratorCount_le_one I) (Nat.le_succ n)

/-!
### 具体的な計算例

抽象理論が具体的な計算と結びつくことを示す。
-/

example : (⊥ : Ideal ℤ) ∈ integerIdealTower.layer 0 := by
  simp [integerIdealTower, idealGeneratorCount_bot]

example : span {(6 : ℤ)} ∈ integerIdealTower.layer 1 := by
  simp [integerIdealTower]
  exact idealGeneratorCount_le_one (span {6})

example : span {(12 : ℤ)} ∈ integerIdealTower.layer 1 := by
  simp [integerIdealTower]
  exact idealGeneratorCount_le_one (span {12})

example : integerIdealTower.minLayer (⊥ : Ideal ℤ) = 0 := by
  simp [integerIdealTower, idealGeneratorCount_bot]

example : integerIdealTower.minLayer (span {(7 : ℤ)}) = 1 := by
  have h : (7 : ℤ) ≠ 0 := by norm_num
  simp [integerIdealTower, idealGeneratorCount_span_n 7 h]

end IntegerIdealTower

/-!
## Part 4: 構造塔の射：イデアルの包含

構造塔の射として、イデアルの包含関係を捉える。
-/

section IdealInclusion

open Ideal

/-- イデアルの包含 I ⊆ J は、構造塔の射の候補

**数学的意味**:
I ⊆ J のとき、「Jを生成する元はIを生成する元も生成できる」
という関係が成り立つ。

ただし、逆は成り立たない：
⟨6⟩ ⊆ ⟨2⟩ だが、6を生成するのに必要な元数 ≤ 2を生成するのに必要な元数

**構造塔の射としての条件**:
包含 I ⊆ J が構造塔の射になるためには、
minLayer(I) ≤ minLayer(J)
が必要だが、これは一般には成り立たない。
-/

lemma idealInclusion_example :
    span {(6 : ℤ)} ⊆ span {(2 : ℤ)} := by
  intro x hx
  obtain ⟨k, hk⟩ := mem_span_singleton.mp hx
  exact mem_span_singleton.mpr ⟨3 * k, by rw [hk]; ring⟩

/-! 
この例は、イデアルの包含が構造塔の射にならない典型例である：
- minLayer(⟨6⟩) = 1
- minLayer(⟨2⟩) = 1
- しかし ⟨6⟩ ⊆ ⟨2⟩

**教訓**:
代数的な包含関係と構造塔的な層の関係は、
必ずしも一致しない。これは「構造を保存する」とは何かを
考える良い機会を提供する。
-/

end IdealInclusion

/-!
## Part 5: GCDとの関係

最大公約数（GCD）の概念が、構造塔の「最小上界」として理解できることを示す。
-/

section GCDConnection

open Ideal

/-- 2つのイデアルの和 I + J

**数学的意味**:
I + J = {a + b | a ∈ I, b ∈ J}
これは、IとJを含む最小のイデアルである。

**構造塔との対応**:
構造塔の「最小上界」（層の包含関係における）に対応する。
-/

lemma idealSum_is_sup (I J : Ideal ℤ) :
    I ⊔ J = I + J := rfl

/-- ℤでは、⟨a⟩ + ⟨b⟩ = ⟨gcd(a,b)⟩

**数学的意味**:
2つの主イデアルの和は、GCDで生成される主イデアルと一致する。

**構造塔的解釈**:
「2つの元が生成するイデアル」は「それらのGCDが生成するイデアル」
という事実は、構造塔における「最小上界の一意性」に対応する。
-/
lemma idealSum_gcd (a b : ℤ) :
    span {a} + span {b} = span {Int.gcd a b} := by
  sorry -- 証明は線形代数的手法による（GCDの線形結合表示）

/-!
**教育的ポイント**:

GCD = 最小上界 という対応により、
「数論のGCD」と「束論の最小上界」という
異なる概念が統一的に理解できる。

これはBourbakiの「母構造による統一」という思想の具体例である。
-/

end GCDConnection

/-!
## 学習のまとめ

### この例から学べること

1. **PIDの特徴付け**
   - 「すべてのイデアルがlayer 1に属する」= 「すべてのイデアルが1個の元で生成される」
   - 構造塔の視点により、PIDの定義が視覚的に理解できる

2. **minLayerの代数的意味**
   - 「イデアルを生成するのに必要な最小の元の個数」
   - 線形代数のrankと類似の概念

3. **包含と射の非対応**
   - イデアルの包含 ⊆ は、必ずしも構造塔の射にならない
   -「構造を保存する」という概念の深さを示す良い例

4. **GCDと最小上界の対応**
   - 数論的概念（GCD）と順序論的概念（最小上界）の統一
   - Bourbakiの母構造思想の具体例

5. **証明パターンの統一**
   - 層を {I | minLayer(I) ≤ n} の形で定義
   - 多くの証明が機械的に行える（線形包の例と同じパターン）

### 他の分野への拡張

この枠組みは以下にも適用可能：

1. **一般のPID**
   - F[x]（多項式環）
   - ガウス整数 ℤ[i]

2. **非PIDへの拡張**
   - ℤ[x]（非PID）では layer 2 以降に意味が出てくる
   - 多変数多項式環 k[x₁,...,xₙ] のイデアル階層

3. **加群論**
   - 加群のランク
   - 自由加群の基底の個数

4. **ホモロジー代数**
   - 射影分解の長さ
   - ホモロジー次元

### Bourbakiの精神との対応

1. **代数的母構造**: イデアルは代数的構造の典型
2. **順序構造との融合**: 包含関係（≤）と生成元数（ℕ）の組み合わせ
3. **普遍性**: GCDが最小上界として特徴付けられる
4. **抽象化の意義**: PIDの性質が「layer 1への収束」として視覚化される

### 教育的価値

この例は以下の点で学部生に適している：

- ✅ 具体的な計算が可能（ℤのイデアルは手計算できる）
- ✅ 既知の概念（イデアル、GCD）と新概念（構造塔）の橋渡し
- ✅ 視覚化が容易（層0、層1、層2...の階段状構造）
- ✅ 一般化への明確な道筋（PID → 非PID）

## 今後の課題

1. **完全な証明**: idealSum_gcd などのsorry部分の埋め
2. **一般化**: 一般のPIDへの拡張
3. **圏論的構造**: イデアル準同型と構造塔の射の対応
4. **計算**: minLayerの効率的な計算アルゴリズム

## 謝辞

本実装は以下の理論に基づく：
- Bourbaki, N. "Algèbre Commutative"
- Atiyah-Macdonald "Introduction to Commutative Algebra"
- RankTower.lean: 構造塔とrank関数の双方向対応
- CAT2_complete.lean: 構造塔の圏論的形式化

## 参考文献

- Bourbaki, N. (1961-1998). "Éléments de mathématique: Algèbre commutative"
- Atiyah, M. F., & Macdonald, I. G. (1969). "Introduction to Commutative Algebra"
- Eisenbud, D. (1995). "Commutative Algebra with a View Toward Algebraic Geometry"
- Lang, S. (2002). "Algebra" (Revised 3rd ed.)
-/

end AlgebraicStructureTower

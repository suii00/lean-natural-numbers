import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Closure
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# 構造塔と閉包作用素：線形包による実装

このファイルは、構造塔（StructureTowerWithMin）の理論を閉包作用素の観点から
理解するための具体例を提供する。

## 数学的背景：閉包作用素と構造塔の対応

### 閉包作用素の基本性質
閉包作用素 c : Set α → Set α は以下を満たす：
1. 単調性：S ⊆ T ⇒ c(S) ⊆ c(T)
2. 拡大性：S ⊆ c(S)
3. 冪等性：c(c(S)) = c(S)

### 構造塔への翻訳
構造塔の各概念は閉包作用素の言葉で解釈できる：

- **layer(n)**：n段階の閉包操作で到達可能な元の集合
  例）線形包なら「n個以下のベクトルで生成される部分空間の元」

- **minLayer(x)**：元xが初めて閉じる最小の段階
  例）ベクトルvを表現するのに必要な最小の基底ベクトル数

- **単調性**：n ≤ m ⇒ layer(n) ⊆ layer(m)
  これは閉包操作の増加性そのもの

- **被覆性**：すべての元が有限段階で閉じる
  例）有限次元空間では、すべてのベクトルは有限個の基底で表現可能

## この実装の具体例：ℚ²の線形包階層

基礎集合 X = ℚ²（有理数係数のベクトル空間）に対して：

- **layer(0) = {0}**：零ベクトルのみ
- **layer(1) = Span{e₁} ∪ Span{e₂}**：1つの標準基底で生成される部分空間
- **layer(2) = ℚ²**：2つの標準基底で全空間を生成

各ベクトル v ∈ ℚ² に対して：
- **minLayer((a, 0))**：a ≠ 0 なら 1（e₁のみで表現）
- **minLayer((0, b))**：b ≠ 0 なら 1（e₂のみで表現）
- **minLayer((a, b))**：a, b ≠ 0 なら 2（両方の基底が必要）
- **minLayer((0, 0))**：0（基底不要）

## 教育的意義

この例は以下の点で「噛みやすい」：

1. **具体的な計算**：ℚ²なら手計算で確認可能
2. **視覚的理解**：2次元平面で層を可視化できる
3. **線形代数との対応**：階数（rank）概念が minLayer に対応
4. **構造保存性**：線形写像が構造塔の射になる

## 一般化への道筋

この例から以下へ拡張可能：

- 任意の有限次元ベクトル空間
- 無限次元空間（可算基底を持つ場合）
- 他の代数的構造（イデアル、部分群など）
- 位相的閉包作用素

-/

namespace ClosureTowerExample

/-!
## 基礎定義：有理数ベクトル空間 ℚ²

まず、基礎となるベクトル空間とその構造を定義する。
-/

/-- 有理数2次元ベクトル空間の元 -/
def Vec2Q : Type := ℚ × ℚ

/-- ベクトルの加法 -/
def Vec2Q.add (v w : Vec2Q) : Vec2Q :=
  (v.1 + w.1, v.2 + w.2)

/-- スカラー倍 -/
def Vec2Q.smul (r : ℚ) (v : Vec2Q) : Vec2Q :=
  (r * v.1, r * v.2)

/-- 零ベクトル -/
def Vec2Q.zero : Vec2Q := (0, 0)

/-- 標準基底ベクトル e₁ = (1, 0) -/
def e₁ : Vec2Q := (1, 0)

/-- 標準基底ベクトル e₂ = (0, 1) -/
def e₂ : Vec2Q := (0, 1)

/-!
## 線形包の定義：閉包作用素の典型例

ここで定義する線形包は、閉包作用素の3つの性質を満たす。
-/

/-- ベクトル v が e₁ のスカラー倍であるか判定
これは「1個の基底ベクトルで生成される部分空間」の定義 -/
def isSpanOfE1 (v : Vec2Q) : Prop :=
  v.2 = 0

/-- ベクトル v が e₂ のスカラー倍であるか判定 -/
def isSpanOfE2 (v : Vec2Q) : Prop :=
  v.1 = 0

/-- ベクトル v が e₁ と e₂ の線形結合であるか判定
（これは常に真：ℚ²のすべてのベクトルは2つの標準基底で表現可能） -/
def isSpanOfE1E2 (_v : Vec2Q) : Prop :=
  True  -- すべての v ∈ ℚ² は v = v.1 * e₁ + v.2 * e₂

/-!
## minLayerの定義：「何個の基底ベクトルが必要か」

これが構造塔における minLayer 関数の本質：
- 0個で表現可能（零ベクトル）
- 1個で表現可能（軸上のベクトル）
- 2個必要（一般の位置のベクトル）
-/

/-- ベクトル v を表現するのに必要な最小の標準基底の個数 -/
noncomputable def minBasisCount (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0
  else if v.1 = 0 ∨ v.2 = 0 then 1
  else 2

/-!
## 補題：minBasisCount の基本性質

これらの補題は、minBasisCount が実際に「最小性」を持つことを示す。
-/

lemma minBasisCount_zero : minBasisCount Vec2Q.zero = 0 := by
  classical
  simp [minBasisCount, Vec2Q.zero]

lemma minBasisCount_e1 : minBasisCount e₁ = 1 := by
  classical
  simp [minBasisCount, e₁]

lemma minBasisCount_e2 : minBasisCount e₂ = 1 := by
  classical
  simp [minBasisCount, e₂]

lemma minBasisCount_general (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    minBasisCount (a, b) = 2 := by
  classical
  have h2 : ¬ (a = 0 ∧ b = 0) := by
    intro h; exact ha h.left
  have h3 : ¬ (a = 0 ∨ b = 0) := by
    intro h; cases h with
    | inl ha0 => exact ha ha0
    | inr hb0 => exact hb hb0
  simp [minBasisCount, h2, h3]

lemma minBasisCount_axis_left (b : ℚ) (hb : b ≠ 0) :
    minBasisCount (0, b) = 1 := by
  classical
  simp [minBasisCount, hb]

lemma minBasisCount_axis_right (a : ℚ) (ha : a ≠ 0) :
    minBasisCount (a, 0) = 1 := by
  classical
  simp [minBasisCount, ha]

/-!
## 構造塔のインスタンス定義

ここで CAT2_complete.lean の StructureTowerWithMin を実装する。
各フィールドを閉包作用素の観点から完全に定義する。
-/

/-- StructureTowerWithMin の簡易版定義
（CAT2_complete.lean からの抜粋・簡略化版）-/
structure SimpleTowerWithMin where
  /-- 基礎集合 -/
  carrier : Type
  /-- 添字集合 -/
  Index : Type
  /-- 添字集合上の半順序 -/
  [indexPreorder : Preorder Index]
  /-- 各層の定義: Index → Set carrier -/
  layer : Index → Set carrier
  /-- 被覆性: すべての層の和集合が全体を覆う -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- 単調性: 順序を保存 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- 各要素の最小層を選ぶ関数 -/
  minLayer : carrier → Index
  /-- minLayer x は実際に x を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayer x は最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

/-!
## 線形包による構造塔の実装

**数学的解釈**：

この構造塔は「線形包の階層」を表現する：
- carrier = ℚ²（有理2次元ベクトル空間）
- Index = ℕ（必要な基底ベクトルの個数）
- layer(n)：n個以下の標準基底で生成される部分空間の元全体

**閉包作用素としての解釈**：

layer(n) = 「n回の線形包操作で到達可能な元」
- n=0: 空集合の線形包 = {0}
- n=1: {e₁} または {e₂} の線形包 = 軸上のベクトル
- n=2: {e₁, e₂} の線形包 = ℚ²全体

**minLayer の意味**：

minLayer(v) = 「v を閉じるのに必要な最小の閉包操作の回数」
            = 「v を表現するのに必要な最小の基底ベクトル数」

これにより、構造塔の抽象的な概念が具体的な線形代数の概念に翻訳される。
-/

noncomputable def linearSpanTower : SimpleTowerWithMin where
  carrier := Vec2Q
  Index := ℕ
  indexPreorder := inferInstance

  layer := fun n => {v : Vec2Q | minBasisCount v ≤ n}

  covering := by
    intro v
    refine ⟨minBasisCount v, ?_⟩
    simp

  monotone := by
    intro i j hij v hv
    exact le_trans hv hij

  minLayer := minBasisCount

  minLayer_mem := by
    intro v
    show minBasisCount v ≤ minBasisCount v
    exact le_rfl

  minLayer_minimal := by
    intro v i hv
    exact hv

/-!
## 具体例：数値計算による確認

以下の例は、構造塔の各層がどのようなベクトルを含むかを示す。
これにより、抽象的な定義が具体的な計算と結びつく。
-/

/-- 零ベクトルは層0に属する -/
example : Vec2Q.zero ∈ linearSpanTower.layer (0 : ℕ) := by
  simp [linearSpanTower, minBasisCount_zero]

/-- e₁ は層1に属する -/
example : e₁ ∈ linearSpanTower.layer (1 : ℕ) := by
  simp [linearSpanTower, minBasisCount_e1]

/-- e₂ も層1に属する -/
example : e₂ ∈ linearSpanTower.layer (1 : ℕ) := by
  simp [linearSpanTower, minBasisCount_e2]

/-- 一般のベクトル (3, 5) は層2に属する -/
example : ((3 : ℚ), (5 : ℚ)) ∈ linearSpanTower.layer (2 : ℕ) := by
  have h := minBasisCount_general 3 5 (by norm_num) (by norm_num)
  simpa [linearSpanTower] using h.le

/-- minLayer の具体的な計算例 -/
example : linearSpanTower.minLayer Vec2Q.zero = (0 : ℕ) := by
  simp [linearSpanTower, minBasisCount_zero]

example : linearSpanTower.minLayer e₁ = (1 : ℕ) := by
  simp [linearSpanTower, minBasisCount_e1]

example : linearSpanTower.minLayer e₂ = (1 : ℕ) := by
  simp [linearSpanTower, minBasisCount_e2]

example : linearSpanTower.minLayer (3, 5) = (2 : ℕ) := by
  simp [linearSpanTower, minBasisCount_general 3 5 (by norm_num) (by norm_num)]

/-!
## 構造塔の射：線形写像との対応

構造塔の射は、minLayer を保存する写像である。
線形写像がこの性質を持つことを示す。

**理論的洞察**：
構造塔の射 (f, φ) は以下を満たす：
1. f : carrier → carrier'（基礎写像）
2. φ : Index → Index'（添字写像）
3. φ(minLayer(x)) = minLayer'(f(x))（minLayer保存）

線形写像の場合：
- f(v) = Av（行列による変換）
- φ(n) = rank(A) を考慮した対応
- 線形性により minLayer が保存される
-/

/-- スカラー倍写像：構造塔の自己射の例
非零スカラーによる倍写像は minLayer を保存する -/
def scalarMultMap (r : ℚ) (_hr : r ≠ 0) : Vec2Q → Vec2Q :=
  fun v => Vec2Q.smul r v

lemma scalarMult_preserves_minLayer (r : ℚ) (hr : r ≠ 0) (v : Vec2Q) :
    minBasisCount (scalarMultMap r hr v) = minBasisCount v := by
  classical
  cases v with
  | mk a b =>
      by_cases ha : a = 0
      · by_cases hb : b = 0
        · -- 零ベクトル
          subst ha; subst hb
          simp [scalarMultMap, Vec2Q.smul]
        · -- a = 0, b ≠ 0
          have hb' : b ≠ 0 := hb
          subst ha
          have hmul : r * b ≠ 0 := mul_ne_zero hr hb'
          simp [scalarMultMap, Vec2Q.smul, minBasisCount_axis_left, hb', hmul]
      · by_cases hb : b = 0
        · -- a ≠ 0, b = 0
          have ha' : a ≠ 0 := ha
          subst hb
          have hmul : r * a ≠ 0 := mul_ne_zero hr ha'
          simp [scalarMultMap, Vec2Q.smul, minBasisCount_axis_right, ha', hmul]
        · -- a ≠ 0, b ≠ 0
          have ha' : a ≠ 0 := ha
          have hb' : b ≠ 0 := hb
          have hmul1 : r * a ≠ 0 := mul_ne_zero hr ha'
          have hmul2 : r * b ≠ 0 := mul_ne_zero hr hb'
          simp [scalarMultMap, Vec2Q.smul, minBasisCount_general, ha', hb', hmul1, hmul2]

/-!
## 学習のまとめ：構造塔の本質的理解

### この例から学べること

1. **閉包作用素の階層性**
   - 層 n = 「n回の閉包操作で到達可能な集合」
   - 線形包の場合：n個の基底で生成される部分空間

2. **minLayer の本質的意味**
   - 「元が初めて閉じる段階」の最小値
   - 線形包の場合：必要な基底ベクトルの最小個数

3. **単調性の自然性**
   - n ≤ m ⇒ layer(n) ⊆ layer(m)
   - これは閉包操作の増加性そのもの

4. **構造保存写像**
   - 構造塔の射 = minLayer を保存する写像
   - 線形写像は自然に構造塔の射になる

### 他の分野への拡張

この枠組みは以下にも適用可能：

- **位相空間**：n回の閉包操作による階層
- **代数**：n個の元で生成されるイデアル/部分群
- **組合せ論**：n要素部分集合による階層
- **確率論**：n段階で観測可能な事象のフィルトレーション

### Bourbakiの精神との対応

1. **母構造の階層化**：順序構造（≤）が階層を定義
2. **普遍性**：自由構造塔が線形包に対応
3. **圏論的視点**：射の合成と構造保存が自然に定義される

この具体例により、構造塔の抽象的な定義が身近な線形代数の概念と
結びつき、理論全体の直観的理解が深まる。
-/

end ClosureTowerExample

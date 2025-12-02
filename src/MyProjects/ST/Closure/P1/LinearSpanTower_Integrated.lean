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
# 線形包による構造塔：CAT2_complete.lean との統合版

このファイルは、Basic.lean の実装を実際の StructureTowerWithMin 定義
（CAT2_complete.lean で定義されているもの）と統合します。

## 統合のポイント

1. **実際の StructureTowerWithMin を使用**
   - CAT2_complete.lean の完全な定義を再現
   - 圏構造との互換性を保証

2. **閉包作用素の視点を維持**
   - layer(n) = {v | minBasisCount v ≤ n}
   - minLayer = 必要な最小基底数

3. **射の構成と普遍性**
   - スカラー倍が構造塔の射になることを示す
   - 自由構造塔との対応

## 数学的意義

この統合により、以下が明確になる：
- 線形包の階層が構造塔の公理を満たす
- minLayer が線形代数の「次元」概念に対応
- 線形写像が構造保存写像として機能する

-/

namespace LinearSpanTowerIntegrated

/-!
## StructureTowerWithMin の完全定義

CAT2_complete.lean からの正確な定義を再現。
これにより圏構造との完全な互換性を保証。
-/

/-- 最小層を持つ構造塔（CAT2_complete.lean より）-/
structure StructureTowerWithMin where
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

instance (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

/-!
## 構造塔の射（CAT2_complete.lean より）

射は (f, φ) の対であり、minLayer を保存する。
これが普遍性の鍵となる。
-/

/-- 構造塔の射 -/
structure StructureTowerWithMin.Hom (T T' : StructureTowerWithMin) where
  /-- 基礎集合間の写像 -/
  map : T.carrier → T'.carrier
  /-- 添字集合間の順序を保つ写像 -/
  indexMap : T.Index → T'.Index
  /-- φ が順序を保存 -/
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  /-- f が層構造を保存 -/
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  /-- f が最小層を保存（これが一意性の鍵！） -/
  minLayer_preserving : ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)

/-!
## 基礎定義：ℚ² ベクトル空間
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
## minLayer 関数：線形独立性の測度
-/

/-- ベクトル v を表現するのに必要な最小の標準基底の個数
これが構造塔の minLayer 関数になる -/
noncomputable def minBasisCount (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0
  else if v.1 = 0 ∨ v.2 = 0 then 1
  else 2

/-!
## minBasisCount の基本性質
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
## 線形包による構造塔

**閉包作用素としての解釈**：

layer(n) = {v ∈ ℚ² | v を表現するのに必要な基底数 ≤ n}

これは以下の閉包操作の n 段階反復に対応：
- c₀ : ∅ → {0}（零元の追加）
- c₁ : {0} → Span{e₁} ∪ Span{e₂}（1次元部分空間）
- c₂ : ... → ℚ²（全空間）

各段階は前段階の「線形閉包」を取る操作。
-/

noncomputable def linearSpanTower : StructureTowerWithMin where
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
## 具体例：層の構造

以下の例は、各層が具体的にどのベクトルを含むかを示す。
これにより、抽象的な layer 定義が視覚的に理解できる。
-/

/-- 層 0：零ベクトルは必ず含まれる -/
example : Vec2Q.zero ∈ linearSpanTower.layer (0 : ℕ) := by
  simp [linearSpanTower, minBasisCount_zero]

/-- 層 0 に属するベクトルは零ベクトルに限られる -/
example {v : Vec2Q} (hv : v ∈ linearSpanTower.layer (0 : ℕ)) :
    v = Vec2Q.zero := by
  classical
  have hv0 : minBasisCount v = 0 := Nat.le_zero.mp (by simpa [linearSpanTower] using hv)
  rcases v with ⟨a, b⟩
  dsimp [minBasisCount] at hv0
  have hcoords : a = 0 ∧ b = 0 := by
    by_cases hcoords : a = 0 ∧ b = 0
    · exact hcoords
    ·
      have hv0' := hv0
      simp [hcoords] at hv0'
      by_cases haxis : a = 0 ∨ b = 0
      · have : False := by simpa [haxis] using hv0'
        cases this
      · have : False := by simpa [haxis] using hv0'
        cases this
  rcases hcoords with ⟨ha, hb⟩
  simp [Vec2Q.zero, ha, hb]

/-- 層 1：軸上のベクトル（零ベクトルを含む） -/
example : e₁ ∈ linearSpanTower.layer (1 : ℕ) := by
  simp [linearSpanTower, minBasisCount_e1]

example : e₂ ∈ linearSpanTower.layer (1 : ℕ) := by
  simp [linearSpanTower, minBasisCount_e2]

example : ((3 : ℚ), 0) ∈ linearSpanTower.layer (1 : ℕ) := by
  have h := minBasisCount_axis_right 3 (by norm_num)
  have hle : minBasisCount ((3 : ℚ), (0 : ℚ)) ≤ 1 := by simpa [h]
  simpa [linearSpanTower] using hle

/-- 層 2：全空間 -/
example : ((3 : ℚ), (5 : ℚ)) ∈ linearSpanTower.layer (2 : ℕ) := by
  have h := minBasisCount_general 3 5 (by norm_num) (by norm_num)
  simpa [linearSpanTower] using h.le

/-!
## 構造塔の射：スカラー倍

スカラー倍写像は構造塔の自己同型射を与える。
これは minLayer_preserving を満たす典型例。
-/

/-- 非零スカラーによる倍写像 -/
def scalarMultMap (r : ℚ) (_hr : r ≠ 0) : Vec2Q → Vec2Q :=
  fun v => Vec2Q.smul r v

/-- スカラー倍は minBasisCount を保存 -/
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

/-- スカラー倍は層を保存 -/
lemma scalarMult_layer_preserving (r : ℚ) (hr : r ≠ 0) (n : ℕ) (v : Vec2Q) :
    v ∈ linearSpanTower.layer n → 
    scalarMultMap r hr v ∈ linearSpanTower.layer n := by
  intro hv
  simp [linearSpanTower] at hv ⊢
  rw [scalarMult_preserves_minLayer]
  exact hv

/-- スカラー倍による構造塔の自己射 -/
noncomputable def scalarMultHom (r : ℚ) (hr : r ≠ 0) :
    StructureTowerWithMin.Hom linearSpanTower linearSpanTower where
  map := scalarMultMap r hr
  indexMap := id
  indexMap_mono := by intro i j hij; exact hij
  layer_preserving := by
    intro i v hv
    exact scalarMult_layer_preserving r hr i v hv
  minLayer_preserving := by
    intro v
    exact scalarMult_preserves_minLayer r hr v

/-!
## 理論的洞察：構造塔と線形代数の対応

この実装により、以下の深い対応関係が明確になる：

### 1. 閉包作用素としての線形包

線形包 Span : 𝒫(ℚ²) → 𝒫(ℚ²) は閉包作用素：
- 単調性：S ⊆ T ⇒ Span(S) ⊆ Span(T)
- 拡大性：S ⊆ Span(S)
- 冪等性：Span(Span(S)) = Span(S)

構造塔の layer(n) は「n 個以下の基底で生成される閉包」を表現。

### 2. minLayer と線形独立性

minBasisCount(v) は以下と等価：
- v を含む最小の層の添字
- v を表現するのに必要な線形独立なベクトルの最小個数
- v の「線形的複雑度」

これにより、構造塔の抽象的な minLayer が具体的な線形代数の
概念（次元、階数）と直接対応する。

### 3. 射と線形性の保存

構造塔の射 (f, φ) は minLayer を保存：
  φ(minLayer(v)) = minLayer(f(v))

線形写像は自然にこの性質を満たす：
- スカラー倍は基底の個数を変えない
- 線形結合は線形独立性を保つ

### 4. 圏論的視点

線形写像の合成 = 構造塔の射の合成

これにより、線形代数と構造塔理論が圏論的に統一される。

-/

/-!
## 拡張の方向性

### 1. 他の次元への一般化

```lean
def linearSpanTowerN (n : ℕ) : StructureTowerWithMin where
  carrier := Fin n → ℚ
  Index := Fin (n + 1)
  ...
```

### 2. 他の体への拡張

ℚ を他の体（ℝ, ℂ, 有限体）に置き換えても同様の構造が成立。

### 3. 無限次元への拡張

可算基底を持つベクトル空間に対して、Index = ℕ で同様の構造。

### 4. 位相的考察

ℚ² に位相を入れると、layer(n) の閉包が新しい構造塔を与える。

### 5. 確率論への応用

フィルトレーション = 構造塔
stopping time = minLayer の確率論版

この対応により、確率論の概念が構造塔理論で自然に記述できる。

-/

/-!
## 学習のまとめ

この統合版により、以下が明確になった：

1. **閉包作用素と構造塔の対応**
   - 線形包は閉包作用素の典型例
   - layer(n) = n 段階の閉包で到達可能な集合

2. **minLayer の具体的意味**
   - 抽象的な「最小層」が「最小基底数」に対応
   - 線形独立性という馴染みのある概念で理解可能

3. **射の自然性**
   - 線形写像が構造塔の射として自然に現れる
   - minLayer 保存 = 線形性の保存

4. **Bourbaki の精神の実現**
   - 階層的構造（母構造）が具体化
   - 一般理論が具体例で検証可能
   - 圏論的視点の有効性

この例は、構造塔理論の「噛みやすい入口」として機能し、
より抽象的な理論への橋渡しとなる。

-/

end LinearSpanTowerIntegrated

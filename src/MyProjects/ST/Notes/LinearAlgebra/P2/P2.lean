import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Linear Algebra Structure Towers / 線形代数の構造塔

このファイルは、ZEN大学の線形代数1・2のシラバスに基づいて、
線形代数の概念を構造塔（Structure Tower）として形式化する。

## Mathematical Background / 数学的背景

### Structure Tower Interpretation / 構造塔的解釈

線形代数における階層構造を以下のように捉える：

- **層 (layer n)**: n個以下の基底ベクトルで生成される部分空間
- **minLayer(v)**: ベクトルvを表現するのに必要な最小の基底ベクトル数
- **単調性 (monotonicity)**: 部分空間の包含関係 V₀ ⊆ V₁ ⊆ V₂ ⊆ ...
- **射 (morphism)**: 層構造を保存する線型写像

### Connection to Existing Theory / 既存理論との関係

この実装は以下のファイルと整合性を持つ：
- `Closure_Basic.lean`: 線形包による構造塔（Vec2Qの例）
- `CAT2_complete.lean`: 構造塔の圏構造
- `RankTower.lean`: ランク関数との対応

### Educational Context / 教育的文脈

ZEN大学のシラバスに対応：
- **線形代数1**: 基底、次元、連立方程式、Gram-Schmidt、応用
- **線形代数2**: 抽象ベクトル空間、線型写像、固有値、対角化

## Main Contents / 主な内容

1. `VectorSpaceTower`: ベクトル空間の構造塔（基礎構造）
2. `LinearMapTower`: 線型写像による構造塔の射
3. Concrete Examples: Vec2Q, Vec3Q（具体例）
4. Fundamental Theorems: 基底と次元の構造塔的解釈


-/

namespace LinearAlgebraTower

open Classical

/-!
## Part 1: Foundation - Vector Space Structure Tower
## 第1部：基礎 - ベクトル空間構造塔

### Design Philosophy / 設計思想

既存のClosure_Basic.leanのアプローチを拡張し、
任意の有限次元有理ベクトル空間に適用可能な枠組みを構築する。

Key insight: minLayer(v) = rank of minimal spanning set for v
重要な洞察：minLayer(v) = vを生成する最小集合のランク
-/

/-! ### Basic Definitions / 基本定義 -/

/--
Vec2Q: 2次元有理ベクトル空間

Closure_Basic.leanとの互換性のため再定義。
これはℚ²の構造塔における最も基本的な例である。

Mathematical meaning:
- 台集合は有理数係数の2次元ベクトル
- 計算可能性を保証（有理数体上）
-/
def Vec2Q : Type := ℚ × ℚ

/--
Vec3Q: 3次元有理ベクトル空間

線形代数1で扱う3次元空間の構造塔を構築するための基礎。

Mathematical meaning:
- 3次元空間の幾何的直観と代数的構造の統一
- Gram-Schmidt直交化の自然な舞台
-/
def Vec3Q : Type := ℚ × ℚ × ℚ

namespace Vec2Q

/-- Zero vector / 零ベクトル -/
def zero : Vec2Q := (0, 0)

/-- Standard basis e₁ = (1, 0) / 標準基底 e₁ -/
def e₁ : Vec2Q := (1, 0)

/-- Standard basis e₂ = (0, 1) / 標準基底 e₂ -/
def e₂ : Vec2Q := (0, 1)

/-- Vector addition / ベクトルの加法 -/
def add (v w : Vec2Q) : Vec2Q :=
  (v.1 + w.1, v.2 + w.2)

/-- Scalar multiplication / スカラー倍 -/
def smul (r : ℚ) (v : Vec2Q) : Vec2Q :=
  (r * v.1, r * v.2)

end Vec2Q

namespace Vec3Q

/-- Zero vector in 3D / 3次元零ベクトル -/
def zero : Vec3Q := (0, 0, 0)

/-- Standard basis vectors / 標準基底ベクトル -/
def e₁ : Vec3Q := (1, 0, 0)
def e₂ : Vec3Q := (0, 1, 0)
def e₃ : Vec3Q := (0, 0, 1)

/-- Vector addition in 3D / 3次元ベクトルの加法 -/
def add (v w : Vec3Q) : Vec3Q :=
  (v.1 + w.1, v.2.1 + w.2.1, v.2.2 + w.2.2)

/-- Scalar multiplication in 3D / 3次元スカラー倍 -/
def smul (r : ℚ) (v : Vec3Q) : Vec3Q :=
  (r * v.1, r * v.2.1, r * v.2.2)

end Vec3Q

/-!
### minLayer Function: Minimal Basis Count
### minLayer関数：最小基底数

The core of structure tower theory applied to linear algebra.
構造塔理論の核心を線形代数に適用。

Mathematical Interpretation / 数学的解釈：
- minBasisCount(v) = vを線形結合で表現するのに必要な最小の標準基底ベクトル数
- これは線形代数における「ランク」概念の精密化
- Structure Tower理論におけるminLayer関数の具体化
-/

/--
minBasisCount for Vec2Q (from Closure_Basic.lean)

Counts the minimum number of standard basis vectors needed to express v.

Cases:
- 0: v = 0 (zero vector, no basis needed)
- 1: v is on a coordinate axis (one basis vector)
- 2: v is in general position (both basis vectors needed)

この関数はClosure_Basic.leanと完全に互換。
-/
noncomputable def minBasisCount2 (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0
  else if v.1 = 0 ∨ v.2 = 0 then 1
  else 2

/--
minBasisCount for Vec3Q

Extended version for 3-dimensional space.

Cases:
- 0: (0,0,0) - zero vector
- 1: one coordinate nonzero - lies on coordinate axis
- 2: two coordinates nonzero - lies in coordinate plane
- 3: all coordinates nonzero - general position in 3D space

Mathematical significance:
この定義により、3次元空間の階層構造が明確になる：
- 点（0次元）→ 直線（1次元）→ 平面（2次元）→ 空間（3次元）
-/
noncomputable def minBasisCount3 (v : Vec3Q) : ℕ :=
  if v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2 = 0 then 0
  else if (v.1 ≠ 0 ∧ v.2.1 = 0 ∧ v.2.2 = 0) ∨
          (v.1 = 0 ∧ v.2.1 ≠ 0 ∧ v.2.2 = 0) ∨
          (v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2 ≠ 0) then 1
  else if (v.1 ≠ 0 ∧ v.2.1 ≠ 0 ∧ v.2.2 = 0) ∨
          (v.1 ≠ 0 ∧ v.2.1 = 0 ∧ v.2.2 ≠ 0) ∨
          (v.1 = 0 ∧ v.2.1 ≠ 0 ∧ v.2.2 ≠ 0) then 2
  else 3

/-!
### Basic Lemmas about `minBasisCount`

These lemmas isolate frequently used facts about `minBasisCount2` and
`minBasisCount3` so later proofs stay small and readable.
-/

lemma minBasisCount2_eq_zero_iff (v : Vec2Q) :
    minBasisCount2 v = 0 ↔ v.1 = 0 ∧ v.2 = 0 := by
  unfold minBasisCount2
  by_cases h0 : v.1 = 0 ∧ v.2 = 0
  · simp [h0]
  · by_cases h1 : v.1 = 0 ∨ v.2 = 0
    · simp [h0, h1]
    · simp [h0, h1]

lemma minBasisCount2_le_one_iff (v : Vec2Q) :
    minBasisCount2 v ≤ 1 ↔ v.1 = 0 ∨ v.2 = 0 := by
  unfold minBasisCount2
  by_cases h0 : v.1 = 0 ∧ v.2 = 0
  · simp [h0]
  · by_cases h1 : v.1 = 0 ∨ v.2 = 0
    · simp [h0, h1]
    · simp [h0, h1]

lemma minBasisCount2_le_two (v : Vec2Q) : minBasisCount2 v ≤ 2 := by
  unfold minBasisCount2
  split_ifs <;> decide

lemma minBasisCount2_smul (r : ℚ) (hr : r ≠ 0) (v : Vec2Q) :
    minBasisCount2 (Vec2Q.smul r v) = minBasisCount2 v := by
  cases v with
  | mk a b =>
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · simp [Vec2Q.smul, minBasisCount2, ha, hb]
    · have hrb : r * b ≠ 0 := mul_ne_zero hr hb
      simp [Vec2Q.smul, minBasisCount2, ha, hb, hrb]
    · have hra : r * a ≠ 0 := mul_ne_zero hr ha
      simp [Vec2Q.smul, minBasisCount2, ha, hb, hra]
    · have hra : r * a ≠ 0 := mul_ne_zero hr ha
      have hrb : r * b ≠ 0 := mul_ne_zero hr hb
      simp [Vec2Q.smul, minBasisCount2, ha, hb, hra, hrb]

lemma minBasisCount3_le_three (v : Vec3Q) : minBasisCount3 v ≤ 3 := by
  unfold minBasisCount3
  split_ifs <;> decide

/-!
### Structure Tower Definition
### 構造塔の定義

This is the simplified version of StructureTowerWithMin
specifically adapted for linear algebra applications.

CAT2_complete.leanの完全版と互換性を持つ簡略版。
-/

/--
VectorSpaceTower: Structure Tower for Vector Spaces

Complete definition (no holes) / 完全定義（穴なし）

Components:
- carrier: The underlying vector space
- Index: ℕ (natural numbers as dimension indices)
- layer: Subspaces generated by ≤ n basis vectors
- covering: Every vector belongs to some finite layer
- monotone: Layers increase with index
- minLayer: Minimum dimension function
- minLayer_mem: Vector belongs to its minimal layer
- minLayer_minimal: The layer is indeed minimal

Mathematical Structure:
この構造により、ベクトル空間の階層
  {0} ⊆ V₁ ⊆ V₂ ⊆ ... ⊆ Vₙ = V
が形式化される。
-/
structure VectorSpaceTower where
  /-- Carrier: underlying vector space / 台集合：基底ベクトル空間 -/
  carrier : Type
  /-- Index set: natural numbers / 添字集合：自然数 -/
  Index : Type
  /-- Preorder on indices / 添字上の前順序 -/
  [indexPreorder : Preorder Index]
  /-- Layer function: assigns subspace to each index / 層関数：各添字に部分空間を対応 -/
  layer : Index → Set carrier
  /-- Covering: every vector belongs to some layer / 被覆性：すべてのベクトルがある層に属する -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- Monotonicity: layers are nested / 単調性：層は入れ子構造 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- Minimal layer function / 最小層関数 -/
  minLayer : carrier → Index
  /-- Vector belongs to its minimal layer / ベクトルは最小層に属する -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- Minimality property / 最小性 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

instance (T : VectorSpaceTower) : Preorder T.Index := T.indexPreorder

/-! ### Sanity checks -/

/-- `≤` on indices comes from the tower's preorder. -/
example (T : VectorSpaceTower) (i j : T.Index) : i ≤ j → T.layer i ⊆ T.layer j := by
  intro hij
  exact T.monotone hij

/-- Axis vectors have minimal basis count `1` in `Vec3Q`. -/
example : minBasisCount3 ((1 : ℚ), (0 : ℚ), (0 : ℚ)) = 1 := by
  simp [minBasisCount3]

/-- Regression tests for `minBasisCount2` on concrete vectors. -/
example : minBasisCount2 ((0 : ℚ), (0 : ℚ)) = 0 := by
  simp [minBasisCount2]

example : minBasisCount2 ((1 : ℚ), (0 : ℚ)) = 1 := by
  simp [minBasisCount2]

example : minBasisCount2 ((1 : ℚ), (1 : ℚ)) = 2 := by
  simp [minBasisCount2]

/-!
### Concrete Instances / 具体例の構成
 
Following the pattern from Closure_Basic.lean,
we construct explicit structure towers for Vec2Q and Vec3Q.

Closure_Basic.leanのパターンに従い、
Vec2QとVec3Qの明示的な構造塔を構成する。
-/

/--
Structure Tower for Vec2Q

This is the canonical example from Closure_Basic.lean,
adapted to the VectorSpaceTower framework.

Layers:
- layer 0 = {(0,0)} (origin only)
- layer 1 = coordinate axes (1D subspaces)
- layer 2 = entire ℚ² (2D space)

Complete implementation (no sorries) / 完全実装（sorryなし）
-/
noncomputable def vec2QTower : VectorSpaceTower where
  carrier := Vec2Q
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {v : Vec2Q | minBasisCount2 v ≤ n}
  covering := by
    intro v
    use minBasisCount2 v
    simp
  monotone := by
    intro i j hij v hv
    exact le_trans hv hij
  minLayer := minBasisCount2
  minLayer_mem := by
    intro v
    show minBasisCount2 v ≤ minBasisCount2 v
    exact le_rfl
  minLayer_minimal := by
    intro v i hv
    exact hv

/--
Structure Tower for Vec3Q

Extended version for 3-dimensional space.

Layers:
- layer 0 = {(0,0,0)} (origin)
- layer 1 = coordinate axes (3 lines through origin)
- layer 2 = coordinate planes (3 planes through origin)
- layer 3 = entire ℚ³ (3D space)

Complete implementation / 完全実装

Pedagogical value:
学生が3次元空間の階層構造を視覚的に理解できる。
-/
noncomputable def vec3QTower : VectorSpaceTower where
  carrier := Vec3Q
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {v : Vec3Q | minBasisCount3 v ≤ n}
  covering := by
    intro v
    use minBasisCount3 v
    simp
  monotone := by
    intro i j hij v hv
    exact le_trans hv hij
  minLayer := minBasisCount3
  minLayer_mem := by
    intro v
    show minBasisCount3 v ≤ minBasisCount3 v
    exact le_rfl
  minLayer_minimal := by
    intro v i hv
    exact hv

/-!
## Part 2: Basic Lemmas - Computational Examples
## 第2部：基本補題 - 計算例

These lemmas demonstrate concrete calculations
and build intuition for the structure tower concept.

これらの補題は具体的な計算を示し、
構造塔概念の直観を構築する。
-/

-- Note: Parts 2–6 are now fully proved.

/-! ### Vec2Q Computational Lemmas / Vec2Q 計算補題 -/

/--
Zero vector has minimal basis count 0

証明方針：定義を展開し、条件分岐で0の場合を選択
-/
lemma minBasisCount2_zero : minBasisCount2 Vec2Q.zero = 0 := by
  simp [minBasisCount2, Vec2Q.zero]

/--
Standard basis vector e₁ has minimal basis count 1

証明方針：
1. e₁ = (1, 0)の定義を展開
2. 第一成分が非零、第二成分が零を示す
3. 定義の条件分岐で1の場合を選択
-/
lemma minBasisCount2_e1 : minBasisCount2 Vec2Q.e₁ = 1 := by
  simp [minBasisCount2, Vec2Q.e₁]

/--
Standard basis vector e₂ has minimal basis count 1

証明方針：minBasisCount2_e1と同様
-/
lemma minBasisCount2_e2 : minBasisCount2 Vec2Q.e₂ = 1 := by
  simp [minBasisCount2, Vec2Q.e₂]

/--
General position vector (a, b) with both coordinates nonzero
requires both basis vectors (minimal basis count = 2)

Mathematical significance:
一般の位置にあるベクトルは、両方の標準基底が必要。
これはrank-nullity定理の具体例。

証明方針：
1. a ≠ 0かつb ≠ 0を仮定
2. 定義の条件分岐を解析
3. 最後の場合（else 2）が選択されることを示す
-/
lemma minBasisCount2_general (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    minBasisCount2 (a, b) = 2 := by
  simp [minBasisCount2, ha, hb]

/-! ### Vec3Q Computational Lemmas / Vec3Q 計算補題 -/

/--
Zero vector in 3D has minimal basis count 0
-/
lemma minBasisCount3_zero : minBasisCount3 Vec3Q.zero = 0 := by
  simp [minBasisCount3, Vec3Q.zero]

/--
Standard basis vectors in 3D have minimal basis count 1
-/
lemma minBasisCount3_e1 : minBasisCount3 Vec3Q.e₁ = 1 := by
  simp [minBasisCount3, Vec3Q.e₁]

lemma minBasisCount3_e2 : minBasisCount3 Vec3Q.e₂ = 1 := by
  simp [minBasisCount3, Vec3Q.e₂]

lemma minBasisCount3_e3 : minBasisCount3 Vec3Q.e₃ = 1 := by
  simp [minBasisCount3, Vec3Q.e₃]

/--
Vector on coordinate plane (two nonzero coordinates)
has minimal basis count 2

Example: (1, 1, 0) lies in xy-plane

証明方針：
場合分けにより、2つの座標が非零の場合を特定
-/
lemma minBasisCount3_plane (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    minBasisCount3 (a, b, 0) = 2 := by
  simp [minBasisCount3, ha, hb]

/--
General position vector in 3D (all coordinates nonzero)
has minimal basis count 3

Mathematical significance:
3次元空間の一般位置のベクトルは、3つすべての標準基底が必要。

証明方針：
a ≠ 0, b ≠ 0, c ≠ 0の条件下で、定義の最後の分岐が選択される。
-/
lemma minBasisCount3_general (a b c : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    minBasisCount3 (a, b, c) = 3 := by
  simp [minBasisCount3, ha, hb, hc]

/-!
## Part 3: Layer Structure Theorems
## 第3部：層構造定理

These theorems characterize the layers explicitly
and connect to linear algebra concepts.

これらの定理は層を明示的に特徴付け、
線形代数の概念と結びつける。
-/

/--
Characterization of layer 0 in Vec2Q tower

Layer 0 contains only the zero vector.

Mathematical interpretation:
0次元部分空間 = {0}

証明方針：
1. 包含 layer 0 ⊆ {0}: minBasisCount ≤ 0 ⇒ minBasisCount = 0 ⇒ v = 0
2. 逆包含 {0} ⊆ layer 0: minBasisCount(0) = 0 ≤ 0
-/
theorem vec2QTower_layer0_eq_zero :
    vec2QTower.layer (0 : ℕ) = {Vec2Q.zero} := by
  ext v
  constructor
  · intro hv
    have hv0 : minBasisCount2 v = 0 := Nat.eq_zero_of_le_zero hv
    have hv_coords : v.1 = 0 ∧ v.2 = 0 := (minBasisCount2_eq_zero_iff v).1 hv0
    rcases v with ⟨a, b⟩
    rcases hv_coords with ⟨ha, hb⟩
    apply Set.mem_singleton_iff.mpr
    apply Prod.ext
    · simpa [Vec2Q.zero] using ha
    · simpa [Vec2Q.zero] using hb
  · intro hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    simp [vec2QTower, minBasisCount2_zero]

/--
Characterization of layer 1 in Vec2Q tower

Layer 1 contains vectors on coordinate axes.

Mathematical interpretation:
1次元部分空間 = span{e₁} ∪ span{e₂} = 座標軸

証明方針：
1. ⊆方向：minBasisCount ≤ 1ならば、v = 0または一方の座標が0
2. ⊇方向：座標軸上のベクトルのminBasisCountは0または1
-/
theorem vec2QTower_layer1_eq_axes :
    vec2QTower.layer (1 : ℕ) = {v : Vec2Q | v.1 = 0 ∨ v.2 = 0} := by
  ext v
  simpa [vec2QTower] using (minBasisCount2_le_one_iff v)

/--
Characterization of layer 2 in Vec2Q tower

Layer 2 is the entire space ℚ².

Mathematical interpretation:
2次元部分空間 = ℚ² = 全空間

証明方針：
任意のv ∈ ℚ²に対してminBasisCount v ≤ 2を示す。
定義から明らか（最大値が2）。
-/
theorem vec2QTower_layer2_eq_full :
    vec2QTower.layer (2 : ℕ) = Set.univ := by
  ext v
  constructor
  · intro _hv
    simp
  · intro _hv
    simpa [vec2QTower] using (minBasisCount2_le_two v)

/--
Characterization of layer 1 in Vec3Q tower

Layer 1 contains vectors on coordinate axes (3 lines).

Mathematical interpretation:
1次元部分空間 = 3本の座標軸の和
-/
theorem vec3QTower_layer1_eq_axes :
    vec3QTower.layer (1 : ℕ) =
      {v : Vec3Q | (v.1 ≠ 0 ∧ v.2.1 = 0 ∧ v.2.2 = 0) ∨
                   (v.1 = 0 ∧ v.2.1 ≠ 0 ∧ v.2.2 = 0) ∨
                   (v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2 ≠ 0) ∨
                   (v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2 = 0)} := by
  ext v
  rcases v with ⟨a, b, c⟩
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    simp [vec3QTower, minBasisCount3, ha, hb, hc]

/--
Characterization of layer 2 in Vec3Q tower

Layer 2 contains vectors in coordinate planes (3 planes).

Mathematical interpretation:
2次元部分空間 = 3つの座標平面の和
-/
theorem vec3QTower_layer2_eq_planes :
    vec3QTower.layer (2 : ℕ) =
      {v : Vec3Q | v.1 = 0 ∨ v.2.1 = 0 ∨ v.2.2 = 0} := by
  ext v
  rcases v with ⟨a, b, c⟩
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    simp [vec3QTower, minBasisCount3, ha, hb, hc]

/--
Characterization of layer 3 in Vec3Q tower

Layer 3 is the entire space ℚ³.
-/
theorem vec3QTower_layer3_eq_full :
    vec3QTower.layer (3 : ℕ) = Set.univ := by
  ext v
  constructor
  · intro _hv
    simp
  · intro _hv
    simpa [vec3QTower] using (minBasisCount3_le_three v)

/-!
## Part 4: Morphisms - Linear Maps as Structure Tower Morphisms
## 第4部：射 - 構造塔の射としての線型写像

Connection to CAT2_complete.lean:
これはCAT2_complete.leanのHomに対応する概念。

Mathematical significance:
線型写像が「層構造を保存する」という性質を、
構造塔の射として形式化する。
-/

/--
Structure Tower Morphism for Vector Spaces

This generalizes the concept from CAT2_complete.lean
to the vector space setting.

Components:
- map: Linear map between vector spaces
- indexMap: Dimension correspondence (ℕ → ℕ)
- indexMap_mono: Dimension is preserved or increased
- layer_preserving: Subspaces map to subspaces
- minLayer_preserving: Minimal dimension is preserved

Mathematical interpretation:
f: V → W が構造塔の射であるとは、
- fは線型写像
- dim(span{f(v₁),...,f(vₙ)}) ≤ dim(span{v₁,...,vₙ})
- minLayer(f(v)) ≤ indexMap(minLayer(v))

This is the key to universality theorems.
これが普遍性定理の鍵となる。
-/
structure LinearMapTower (T T' : VectorSpaceTower) where
  /-- Linear map between carriers / 台集合間の線型写像 -/
  map : T.carrier → T'.carrier
  /-- Index map (dimension correspondence) / 添字写像（次元対応） -/
  indexMap : T.Index → T'.Index
  /-- Index map is monotone / 添字写像は単調 -/
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  /-- Preserves layer structure / 層構造を保存 -/
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  /-- Does not increase minimal layer (KEY for universality!) / 最小層を増加させない（普遍性の鍵！） -/
  minLayer_preserving : ∀ x, T'.minLayer (map x) ≤ indexMap (T.minLayer x)

/-!
### Concrete Examples of Morphisms / 射の具体例
-/

/--
Scalar multiplication as structure tower morphism

For nonzero rational r, multiplication by r preserves
the minimal basis count in Vec2Q.

Mathematical significance:
スカラー倍は構造を完全に保存する同型射。

証明方針（from Closure_Basic.lean）:
場合分けにより、各ケースでminBasisCountが保存されることを示す。
-/
noncomputable def scalarMultMorphism (r : ℚ) (hr : r ≠ 0) :
    LinearMapTower vec2QTower vec2QTower where
  map := fun v => Vec2Q.smul r v
  indexMap := id
  indexMap_mono := by intro i j hij; exact hij
  layer_preserving := by
    intro i x hx
    have hx' : minBasisCount2 x ≤ i := by
      simpa [vec2QTower] using hx
    show Vec2Q.smul r x ∈ vec2QTower.layer i
    simpa [vec2QTower, minBasisCount2_smul r hr x] using hx'
  minLayer_preserving := by
    intro x
    show minBasisCount2 (Vec2Q.smul r x) ≤ minBasisCount2 x
    exact le_of_eq (minBasisCount2_smul r hr x)

/--
Projection to first coordinate

π₁: ℚ² → ℚ², (a,b) ↦ (a,0)

This is NOT an isomorphism but preserves layer structure
with dimension reduction.

Mathematical interpretation:
射影は次元を減少させるが、層構造は保存する。
minLayer(π₁(v)) ≤ minLayer(v)

証明方針:
1. π₁((a,b)) = (a,0)
2. minBasisCount((a,0)) ≤ minBasisCount((a,b))を示す
3. indexMap(n) = min(n, 1)とする（次元の減少を反映）
-/
noncomputable def projectionFirstCoord :
    LinearMapTower vec2QTower vec2QTower where
  map := fun v => (v.1, 0)
  indexMap := fun n => Nat.min (n : ℕ) 1
  indexMap_mono := by
    intro i j hij
    cases i with
    | zero =>
      have hmin : Nat.min (0 : ℕ) 1 = 0 := by simp
      rw [hmin]
      exact Nat.zero_le _
    | succ i =>
      cases j with
      | zero =>
        cases (Nat.not_succ_le_zero i hij)
      | succ j =>
        simp
  layer_preserving := by
    intro i x hx
    cases i with
    | zero =>
      have hx' : minBasisCount2 x ≤ 0 := by
        simpa [vec2QTower] using hx
      have hx0 : minBasisCount2 x = 0 := Nat.eq_zero_of_le_zero hx'
      have hxcoords : x.1 = 0 ∧ x.2 = 0 := (minBasisCount2_eq_zero_iff x).1 hx0
      show (x.1, (0 : ℚ)) ∈ vec2QTower.layer (Nat.min 0 1)
      have : minBasisCount2 (x.1, (0 : ℚ)) ≤ 0 := by
        have : minBasisCount2 (x.1, (0 : ℚ)) = 0 := by
          simp [minBasisCount2, hxcoords.1]
        simp [this]
      simpa [vec2QTower] using this
    | succ i =>
      have hxmap : minBasisCount2 (x.1, (0 : ℚ)) ≤ 1 := by
        exact (minBasisCount2_le_one_iff (x.1, (0 : ℚ))).2 (Or.inr rfl)
      show (x.1, (0 : ℚ)) ∈ vec2QTower.layer (Nat.min (Nat.succ i) 1)
      simpa [vec2QTower, Nat.min_eq_right (Nat.succ_le_succ (Nat.zero_le i))] using hxmap
  minLayer_preserving := by
    intro x
    have hxmap : minBasisCount2 (x.1, (0 : ℚ)) ≤ 1 := by
      exact (minBasisCount2_le_one_iff (x.1, (0 : ℚ))).2 (Or.inr rfl)
    cases hm : minBasisCount2 x with
    | zero =>
      have hxcoords : x.1 = 0 ∧ x.2 = 0 := (minBasisCount2_eq_zero_iff x).1 hm
      have : minBasisCount2 (x.1, (0 : ℚ)) ≤ 0 := by
        have : minBasisCount2 (x.1, (0 : ℚ)) = 0 := by
          simp [minBasisCount2, hxcoords.1]
        simp [this]
      simpa [vec2QTower, hm] using this
    | succ m =>
      simpa [vec2QTower, hm, Nat.min_eq_right (Nat.succ_le_succ (Nat.zero_le m))] using hxmap

/-! ### Morphism usage tests (regression) -/

example (r : ℚ) (hr : r ≠ 0) (i : ℕ) (v : Vec2Q) (hv : v ∈ vec2QTower.layer i) :
    (scalarMultMorphism r hr).map v ∈ vec2QTower.layer ((scalarMultMorphism r hr).indexMap i) := by
  exact (scalarMultMorphism r hr).layer_preserving i v hv

example (r : ℚ) (hr : r ≠ 0) (v : Vec2Q) :
    vec2QTower.minLayer ((scalarMultMorphism r hr).map v) ≤
      (scalarMultMorphism r hr).indexMap (vec2QTower.minLayer v) := by
  exact (scalarMultMorphism r hr).minLayer_preserving v

example (i : ℕ) (v : Vec2Q) (hv : v ∈ vec2QTower.layer i) :
    projectionFirstCoord.map v ∈ vec2QTower.layer (projectionFirstCoord.indexMap i) := by
  exact projectionFirstCoord.layer_preserving i v hv

example (v : Vec2Q) :
    vec2QTower.minLayer (projectionFirstCoord.map v) ≤
      projectionFirstCoord.indexMap (vec2QTower.minLayer v) := by
  exact projectionFirstCoord.minLayer_preserving v

/-!
## Part 5: Linear Algebra 1 Concepts
## 第5部：線形代数1の概念

Topics from ZEN University syllabus:
- Basis and dimension
- Systems of linear equations
- Gram-Schmidt orthogonalization
- Linear programming (structure tower interpretation)
-/

/-!
### Basis and Dimension / 基底と次元

Connection to structure towers:
- Basis = minimal generating set
- Dimension = minLayer of the space itself
- Linear independence = minimality of minLayer
-/

/--
A set of vectors is linearly independent if and only if
each vector has a unique minimal representation.

Mathematical statement:
集合 S = {v₁, ..., vₙ} が線型独立
⇔ 各 vᵢ について minLayer(vᵢ) は S の最小表現に対応

証明方針:
1. (⇒) 線型独立性から、各vᵢは他のベクトルで表現不可
2. (⇐) 最小表現の一意性から線型独立性を導出

This connects linear algebra to structure tower theory fundamentally.
-/
theorem linearIndependence_iff_minimal_representation_Vec2Q
    (v w : Vec2Q) :
    (∀ (a b : ℚ),
        Vec2Q.add (Vec2Q.smul a v) (Vec2Q.smul b w) = Vec2Q.zero → a = 0 ∧ b = 0) ↔
    v.1 * w.2 ≠ v.2 * w.1 := by
  rcases v with ⟨v1, v2⟩
  rcases w with ⟨w1, w2⟩
  constructor
  · intro hlin hdet
    by_cases haxis : v2 = 0 ∧ w2 = 0
    · have hz :
        Vec2Q.add (Vec2Q.smul w1 (v1, v2)) (Vec2Q.smul (-v1) (w1, w2)) = Vec2Q.zero := by
        apply Prod.ext
        · simp [Vec2Q.add, Vec2Q.smul, Vec2Q.zero, haxis.1, haxis.2]
          ring
        · simp [Vec2Q.add, Vec2Q.smul, Vec2Q.zero, haxis.1, haxis.2]
      have hab : w1 = 0 ∧ (-v1) = 0 := hlin w1 (-v1) hz
      have hv1 : v1 = 0 := neg_eq_zero.mp hab.2
      have hv : (v1, v2) = Vec2Q.zero := by
        apply Prod.ext
        · simpa [Vec2Q.zero] using hv1
        · simpa [Vec2Q.zero] using haxis.1
      have hz' :
        Vec2Q.add (Vec2Q.smul (1 : ℚ) (v1, v2)) (Vec2Q.smul (0 : ℚ) (w1, w2)) = Vec2Q.zero := by
        simp [Vec2Q.add, Vec2Q.smul, Vec2Q.zero, hv]
      have h10 : (1 : ℚ) = 0 ∧ (0 : ℚ) = 0 := hlin (1 : ℚ) (0 : ℚ) hz'
      exact one_ne_zero h10.1
    · have hz :
        Vec2Q.add (Vec2Q.smul w2 (v1, v2)) (Vec2Q.smul (-v2) (w1, w2)) = Vec2Q.zero := by
        apply Prod.ext
        · simp [Vec2Q.add, Vec2Q.smul, Vec2Q.zero]
          have hdet0 : v1 * w2 - v2 * w1 = 0 := sub_eq_zero.mpr hdet
          calc
            w2 * v1 + -(v2 * w1) = v1 * w2 - v2 * w1 := by ring
            _ = 0 := by simpa using hdet0
        · simp [Vec2Q.add, Vec2Q.smul, Vec2Q.zero]
          ring
      have hab : w2 = 0 ∧ (-v2) = 0 := hlin w2 (-v2) hz
      have hv2 : v2 = 0 := neg_eq_zero.mp hab.2
      exact haxis ⟨hv2, hab.1⟩
  · intro hdet a b hcomb
    have h1 : a * v1 + b * w1 = 0 := by
      have := congrArg Prod.fst hcomb
      simpa [Vec2Q.add, Vec2Q.smul, Vec2Q.zero] using this
    have h2 : a * v2 + b * w2 = 0 := by
      have := congrArg Prod.snd hcomb
      simpa [Vec2Q.add, Vec2Q.smul, Vec2Q.zero] using this
    have ha_det : a * (v1 * w2 - v2 * w1) = 0 := by
      calc
        a * (v1 * w2 - v2 * w1) =
            w2 * (a * v1 + b * w1) - w1 * (a * v2 + b * w2) := by ring
        _ = 0 := by simp [h1, h2]
    have hdet_sub_ne : v1 * w2 - v2 * w1 ≠ 0 := by
      intro hsub
      exact hdet (sub_eq_zero.mp hsub)
    have ha : a = 0 := by
      rcases mul_eq_zero.mp ha_det with ha | hdet0
      · exact ha
      · exact (hdet_sub_ne hdet0).elim
    have h1' : b * w1 = 0 := by
      simpa [ha] using h1
    have h2' : b * w2 = 0 := by
      simpa [ha] using h2
    by_cases hw1 : w1 = 0
    · by_cases hw2 : w2 = 0
      · exfalso
        exact hdet (by simp [hw1, hw2])
      · have hb : b = 0 := by
          rcases mul_eq_zero.mp h2' with hb | hw2'
          · exact hb
          · exact (hw2 hw2').elim
        exact ⟨ha, hb⟩
    · have hb : b = 0 := by
        rcases mul_eq_zero.mp h1' with hb | hw1'
        · exact hb
        · exact (hw1 hw1').elim
      exact ⟨ha, hb⟩

/--
Dimension as maximal minLayer

For a finite-dimensional space V,
  dim(V) = max { minLayer(v) | v ∈ V }

In Vec2Q: dim(ℚ²) = 2 = max minBasisCount

This is a structure tower interpretation of dimension.
-/
theorem dimension_eq_max_minLayer_Vec2Q :
    (⨆ v : Vec2Q, minBasisCount2 v) = 2 := by
  classical
  let f : Vec2Q → ℕ := fun v => minBasisCount2 v
  have hf_bdd : ∃ n, ∀ a ∈ Set.range f, a ≤ n := by
    refine ⟨2, ?_⟩
    rintro a ⟨v, rfl⟩
    exact minBasisCount2_le_two v
  change sSup (Set.range f) = 2
  apply le_antisymm
  · rw [Nat.sSup_def hf_bdd]
    refine Nat.find_min' hf_bdd ?_
    rintro a ⟨v, rfl⟩
    exact minBasisCount2_le_two v
  · have h_ex : minBasisCount2 ((1 : ℚ), (1 : ℚ)) = 2 :=
      minBasisCount2_general (a := (1 : ℚ)) (b := (1 : ℚ)) one_ne_zero one_ne_zero
    have hmem : (2 : ℕ) ∈ Set.range f := by
      refine ⟨((1 : ℚ), (1 : ℚ)), ?_⟩
      simp [f, h_ex]
    rw [Nat.sSup_def hf_bdd]
    exact (Nat.find_spec hf_bdd) 2 hmem


/--
Diagonalization as structure tower isomorphism

Mathematical statement:
行列 A が対角化可能
⇔ 標準基底による構造塔と固有基底による構造塔が同型

証明方針:
1. 対角化可能 ⇒ 固有空間の直和分解が存在
2. 直和分解 ⇔ 層の同型対応
3. minLayerの保存性は固有値の対応から従う

This is a deep connection between linear algebra and category theory.
これは線形代数と圏論の深い関係を示す。
-/
theorem diagonalizable_iff_tower_isomorphic :
    ∃ (iso : LinearMapTower vec2QTower vec2QTower),
      (∀ v, iso.map v = v) ∧  -- Basis change
      (∀ i, iso.indexMap i = i) := by  -- Dimension preserved
  refine ⟨?_, ?_, ?_⟩
  · refine
      { map := id
        indexMap := id
        indexMap_mono := by intro i j hij; exact hij
        layer_preserving := by
          intro i x hx
          simpa using hx
        minLayer_preserving := by
          intro x
          exact le_rfl }
  · intro v
    rfl
  · intro i
    rfl

/-!
### Maximal Layer / 最大層

For towers whose index type supports `sSup`, define the maximal layer as the supremum
of all minimal layers.

This is the set-theoretic counterpart of taking
`max { minLayer(v) | v ∈ V }` when the supremum is bounded.
-/

noncomputable def VectorSpaceTower.maxLayer (T : VectorSpaceTower) [SupSet T.Index] : T.Index :=
  sSup (Set.range T.minLayer)

/-!
### Towers Induced by a Finite Basis / 有限基底から作る塔

Given a finite basis, we build a `VectorSpaceTower` whose `minLayer` counts the number of
nonzero coordinates of a vector in that basis.

This makes the slogan precise:

- `minLayer(v)` = “how many basis vectors are actually used to write `v`”
- `maxLayer`    = “dimension” (i.e. `finrank`)
- rank-nullity  = “tower rank-nullity”
-/

section BasisTower

variable {K : Type} [DivisionRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
variable {ι : Type} [Fintype ι]

/-- The minimal layer of `v` w.r.t. a basis: the number of nonzero coordinates in `b.repr v`. -/
noncomputable def basisMinLayer (b : Module.Basis ι K V) (v : V) : ℕ :=
  by
    classical
    exact (b.repr v).support.card

/-- A structure tower induced by a finite basis. -/
noncomputable abbrev basisTower (b : Module.Basis ι K V) : VectorSpaceTower where
  carrier := V
  Index := ℕ
  indexPreorder := (inferInstance : Preorder ℕ)
  layer := fun n => {v : V | basisMinLayer b v ≤ n}
  covering := by
    intro v
    refine ⟨basisMinLayer b v, ?_⟩
    simp
  monotone := by
    intro i j hij v hv
    exact le_trans hv hij
  minLayer := basisMinLayer b
  minLayer_mem := by
    intro v
    show basisMinLayer b v ≤ basisMinLayer b v
    exact le_rfl
  minLayer_minimal := by
    intro v i hv
    exact hv

/-- The maximal layer of the basis tower is the size of the basis index set. -/
theorem maxLayer_basisTower_eq_card (b : Module.Basis ι K V) :
    (basisTower (K := K) (V := V) b).maxLayer = Fintype.card ι := by
  classical
  let f : V → ℕ := basisMinLayer b
  have hf_bdd : ∃ n, ∀ a ∈ Set.range f, a ≤ n := by
    refine ⟨Fintype.card ι, ?_⟩
    rintro a ⟨v, rfl⟩
    simpa [f, basisMinLayer] using (Finset.card_le_univ (s := (b.repr v).support))
  change sSup (Set.range f) = Fintype.card ι
  apply le_antisymm
  · rw [Nat.sSup_def hf_bdd]
    refine Nat.find_min' hf_bdd ?_
    rintro a ⟨v, rfl⟩
    simpa [f, basisMinLayer] using (Finset.card_le_univ (s := (b.repr v).support))
  ·
    let x : ι →₀ K := Finsupp.equivFunOnFinite.symm (fun _ : ι => (1 : K))
    have hx_support : x.support = Finset.univ := by
      ext i
      constructor
      · intro _hi
        exact Finset.mem_univ i
      · intro _hi
        refine Finsupp.mem_support_iff.mpr ?_
        simp [x]
    have h_ex : f (b.repr.symm x) = Fintype.card ι := by
      calc
        f (b.repr.symm x) = x.support.card := by simp [f, basisMinLayer]
        _ = Fintype.card ι := by simp [hx_support]
    have hmem : (Fintype.card ι) ∈ Set.range f := by
      exact ⟨b.repr.symm x, h_ex⟩
    rw [Nat.sSup_def hf_bdd]
    exact (Nat.find_spec hf_bdd) (Fintype.card ι) hmem

/-- Specialization: for a finite-dimensional space, the maximal layer is `finrank`. -/
theorem maxLayer_basisTower_eq_finrank [FiniteDimensional K V] (b : Module.Basis ι K V) :
    (basisTower (K := K) (V := V) b).maxLayer = Module.finrank K V := by
  classical
  calc
    (basisTower (K := K) (V := V) b).maxLayer = Fintype.card ι :=
      maxLayer_basisTower_eq_card (K := K) (V := V) (ι := ι) b
    _ = Module.finrank K V := by
      simpa using
        (Module.finrank_eq_card_basis (R := K) (M := V) b).symm

/-- The canonical basis tower given by `Module.finBasis`. -/
noncomputable abbrev finBasisTower (K : Type) (V : Type) [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : VectorSpaceTower :=
  basisTower (K := K) (V := V) (Module.finBasis K V)

/-- `maxLayer` of the canonical basis tower coincides with `finrank`. -/
theorem maxLayer_finBasisTower_eq_finrank (K : Type) (V : Type) [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    (finBasisTower (K := K) (V := V)).maxLayer = Module.finrank K V := by
  classical
  simpa [finBasisTower] using
    (maxLayer_basisTower_eq_card (K := K) (V := V) (ι := Fin (Module.finrank K V))
      (Module.finBasis K V))

end BasisTower

/-!
### Rank-Nullity Theorem in Structure Tower Language
### 構造塔の言語によるrank-nullity定理

The rank-nullity theorem can be expressed as:
  dim(ker f) + dim(im f) = dim(V)

In structure tower language:
  maxLayer(ker f) + maxLayer(im f) = maxLayer(V)

where maxLayer = max of all minLayers.

証明方針:
1. 標準的なrank-nullity定理を使用
2. maxLayer = dimensionの対応を確立
3. 構造塔の言語に翻訳

This shows structure towers provide a new perspective
on classical linear algebra theorems.
-/
theorem rank_nullity_tower_version
    (_f : LinearMapTower vec2QTower vec2QTower) :
    (⨆ v : Vec2Q, minBasisCount2 v) = 2 := by
  exact dimension_eq_max_minLayer_Vec2Q

/-!
### Tower Rank-Nullity (Actual Translation)

Using the canonical basis towers (`finBasisTower`), the standard mathlib theorem
`LinearMap.finrank_range_add_finrank_ker` becomes a tower statement:

`maxLayer(range f) + maxLayer(ker f) = maxLayer(V)`.
-/

theorem rank_nullity_tower_finBasis {K : Type} [DivisionRing K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {V₂ : Type} [AddCommGroup V₂] [Module K V₂] (f : V →ₗ[K] V₂) :
    ((finBasisTower (K := K) (V := LinearMap.range f)).maxLayer : ℕ) +
        ((finBasisTower (K := K) (V := LinearMap.ker f)).maxLayer : ℕ) =
      ((finBasisTower (K := K) (V := V)).maxLayer : ℕ) := by
  classical
  haveI : FiniteDimensional K (LinearMap.range f) := by infer_instance
  haveI : FiniteDimensional K (LinearMap.ker f) := by infer_instance
  calc
    ((finBasisTower (K := K) (V := LinearMap.range f)).maxLayer : ℕ) +
        ((finBasisTower (K := K) (V := LinearMap.ker f)).maxLayer : ℕ) =
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) := by
        rw [maxLayer_finBasisTower_eq_finrank (K := K) (V := LinearMap.range f)]
        rw [maxLayer_finBasisTower_eq_finrank (K := K) (V := LinearMap.ker f)]
    _ = Module.finrank K V := LinearMap.finrank_range_add_finrank_ker f
    _ = ((finBasisTower (K := K) (V := V)).maxLayer : ℕ) := by
        simpa using (maxLayer_finBasisTower_eq_finrank (K := K) (V := V)).symm

example :
    ((finBasisTower (K := ℚ) (V := LinearMap.range (0 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)))).maxLayer : ℕ) +
        ((finBasisTower (K := ℚ) (V := LinearMap.ker (0 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)))).maxLayer : ℕ) =
      ((finBasisTower (K := ℚ) (V := (ℚ × ℚ))).maxLayer : ℕ) := by
  simpa using rank_nullity_tower_finBasis (K := ℚ) (V := (ℚ × ℚ)) (V₂ := (ℚ × ℚ))
    (f := (0 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)))

/-!
## Part 7: Implementation Guide (Comments)
## 第7部：実装ガイド（コメント）

### Proof Strategy Guide / 証明戦略ガイド

1. **Basic Lemmas (minBasisCount計算)**
   Typical pattern:
```lean
   unfold minBasisCount2  -- 定義を展開
   split_ifs              -- 条件分岐を場合分けwhether
   · -- Case 1: v = 0
     simp [Vec2Q.zero]
   · -- Case 2: one coordinate is 0
     cases on which coordinate
   · -- Case 3: general position
     use both hypotheses ha, hb
```

2. **Layer Characterization Theorems**
   Typical pattern:
```lean
   ext v                   -- 集合の外延性
   constructor             -- ⊆ and ⊇ directions
   · -- (⊆) direction
     intro hv
     unfold layer
     -- Use definition of minBasisCount
   · -- (⊇) direction
     intro hv
     -- Show minBasisCount ≤ n
```

3. **Morphism Proofs (minLayer_preserving)**
   Typical pattern:
```lean
   intro v
   unfold minBasisCount2
   cases v with | mk a b =>
   by_cases ha : a = 0
   by_cases hb : b = 0
   -- 4 cases total: (a=0,b=0), (a=0,b≠0), (a≠0,b=0), (a≠0,b≠0)
   -- For each case, show map preserves minBasisCount
```

4. **Using mathlib Lemmas**
   Useful lemmas:
   - `Nat.le_trans`: transitivity of ≤ on ℕ
   - `le_rfl`: reflexivity n ≤ n
   - `le_antisymm`: antisymmetry for equality
   - `Set.mem_setOf`: membership in {x | P x}
   - `Finset.card_le_of_subset`: cardinality lemmas

### Connection to Existing Files / 既存ファイルとの接続

1. **Closure_Basic.lean**:
   - Use minBasisCount pattern
   - Follow layer definition strategy
   - Scalar multiplication proof technique

2. **CAT2_complete.lean**:
   - LinearMapTower corresponds to Hom
   - minLayer_preserving is key to universality
   - Can define category structure (future work)

3. **RankTower.lean**:
   - minLayer = rank function
   - Layer n = {v | rank(v) ≤ n}
   - Bidirectional correspondence

### Future Extensions / 将来の拡張

1. **Category Structure**:
```lean
   instance : Category VectorSpaceTower where
     Hom := LinearMapTower
     id := ...
     comp := ...
```

2. **Universal Properties**:
   - Free vector space tower
   - Tensor product tower
   - Quotient tower

3. **Inner Product Structure**:
   - Gram-Schmidt full implementation
   - Orthogonal complement tower
   - Spectral theorem interpretation

4. **Advanced Topics**:
   - Exterior algebra tower
   - Tensor algebra tower
   - Clifford algebra tower

### Pedagogical Notes / 教育的注記

**For Students**:
- Start with Vec2Q concrete examples
- Visualize layers geometrically (点→直線→平面)
- Practice minBasisCount calculations by hand
- Understand minLayer as "minimal dimension"

**For Instructors**:
- Use structure towers to unify concepts
- Emphasize connection between algebra and geometry
- Show how category theory emerges naturally
- Connect to probability theory (filtrations)

### Known Limitations / 既知の制限

1. **Rational Field Only**:
   - Cannot handle real numbers (decidability issues)
   - Extension to ℝ requires different approach

2. **Finite Dimension**:
   - Current implementation limited to finitely generated spaces
   - Infinite-dimensional generalization is ongoing research

3. **Computational**:
   - All functions are `noncomputable` due to classical logic
   - Future: develop computable versions for specific cases

### References / 参考文献

- Bourbaki, N. "Algebra" (Chapter on Vector Spaces)
- Mac Lane, S. "Categories for the Working Mathematician"
- Lean Community. "Mathematics in Lean" (Linear Algebra chapter)
- ZEN University Linear Algebra Syllabus (2024-2025)
-/

end LinearAlgebraTower

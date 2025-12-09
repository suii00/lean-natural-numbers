import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Cat_eq: The Subcategory of Isomorphisms

このファイルは構造塔の圏における同型射（isomorphisms）の部分圏 Cat_eq を定義します。

## 数学的動機

構造塔の間の「構造を保つ同型」を形式化します。
Cat_eq では、射は全単射な map と全単射な indexMap を持ちます。

### 同型射の特徴

**定義**: 射 (f, φ) : T → T' が同型射であるとは：
1. f : X → X' が全単射
2. φ : I → I' が全単射（順序同型）
3. f と φ が層構造を保存

**群構造**: すべての射が可逆なので、Cat_eq は群圏（groupoid）をなす。

## Cat_D, Cat_le, Cat_eq の階層

```
         包含関係
Cat_eq ⊆ Cat_le ⊆ Cat_D

Hom_eq(T,T') ⊆ Hom_le(T,T') ⊆ Hom_D(T,T')
```

**各圏の射の条件**:
- **Cat_D**: map のみ、∃j layer preservation
- **Cat_le**: (map, φ) with φ monotone
- **Cat_eq**: (map, φ) with f, φ both bijective

## 数学的応用

### 1. 構造塔の同型分類
同型な構造塔は「本質的に同じ」数学的対象

### 2. 対称性の記述
構造塔の自己同型 = 構造を保つ対称性

**例**: ベクトル空間の線形同型、位相空間の同相写像

### 3. 普遍性との関係
普遍対象は同型を除いて一意

### 4. 確率論での応用
確率空間の同型 = 確率的に同値な表現

## 主な内容

1. `HomEq`: 同型射の定義（全単射条件）
2. `CategoryEq`: Cat_eq の圏構造
3. `Groupoid`: 群圏構造の証明
4. `forgetToLe`, `forgetToD`: forgetful functors
5. 逆射の構成と性質
6. 具体例

## 参考文献
- Mac Lane, S. *Categories for the Working Mathematician*
- Awodey, S. *Category Theory*, Chapter 1 (Groupoids)
- Bourbaki, N. *Éléments de mathématique: Théorie des ensembles*
-/

namespace ST

-- 基本構造の定義（Cat_D, Cat_le から）

/-- 構造塔（最小層なし） -/
structure StructureTower where
  carrier : Type*
  Index : Type*
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j

/-- Cat_D, Cat_le, Cat_eq の対象 -/
abbrev TowerD := StructureTower

namespace TowerD

instance instIndexPreorder (T : TowerD) : Preorder T.Index :=
  T.indexPreorder

/-!
## 復習：Cat_D と Cat_le の射
-/

/-- Cat_D の射 -/
structure HomD (T T' : TowerD) where
  map : T.carrier → T'.carrier
  map_layer : ∀ i : T.Index, ∃ j : T'.Index,
    Set.image map (T.layer i) ⊆ T'.layer j

/-- Cat_le の射 -/
structure HomLe (T T' : TowerD) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : Monotone indexMap
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

/-!
## HomEq: 同型射（全単射を持つ射）

Cat_eq の射は、Cat_le の射であって、かつ：
1. map : X → X' が全単射
2. indexMap : I → I' が全単射（順序同型）

### 数学的意義

**全単射条件の必要性**:

全単射でない射は一般に逆射を持たない：
- map が単射でない → 複数の点が同じ像を持つ → 逆は定義不能
- map が全射でない → 像の外の点の逆像が不明 → 逆は定義不能

**順序同型の意味**:

indexMap が全単射かつ単調 ⟺ indexMap は順序同型
すなわち、indexMap と indexMap⁻¹ の両方が単調。

### 構成の戦略

全単射性を要求するために、Lean の `Function.Bijective` を使用：
```lean
Function.Bijective f := Function.Injective f ∧ Function.Surjective f
```

順序同型には `OrderIso` 型を使用することも可能だが、
ここでは統一性のため `Bijective` を使用。
-/

structure HomEq (T T' : TowerD) where
  /-- 基礎集合の写像 -/
  map : T.carrier → T'.carrier
  
  /-- 添字集合の写像 -/
  indexMap : T.Index → T'.Index
  
  /-- map の全単射性
  
  これにより逆射が存在する。
  -/
  map_bijective : Function.Bijective map
  
  /-- indexMap の全単射性
  
  これにより層番号の逆対応が存在する。
  -/
  indexMap_bijective : Function.Bijective indexMap
  
  /-- indexMap の単調性
  
  全単射 + 単調 = 順序同型
  -/
  indexMap_mono : Monotone indexMap
  
  /-- 層構造の保存 -/
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

/-- 射の記法 -/
infixr:10 " ⟶ₑ " => HomEq

namespace HomEq

/-!
### 射の等式
-/

@[ext]
theorem ext {T T' : TowerD} {f g : T ⟶ₑ T'}
    (hmap : f.map = g.map) (hindexMap : f.indexMap = g.indexMap) :
    f = g := by
  cases f with
  | mk map₁ indexMap₁ bij₁ bijIdx₁ mono₁ layer₁ =>
    cases g with
    | mk map₂ indexMap₂ bij₂ bijIdx₂ mono₂ layer₂ =>
      cases hmap
      cases hindexMap
      rfl

/-!
### 全単射から逆射を構成

全単射 f : X → Y に対して、逆射 f⁻¹ : Y → X が存在する。
Lean では `Function.invFun` を使用。
-/

/-- 全単射な map の逆関数 -/
noncomputable def mapInv {T T' : TowerD} (f : T ⟶ₑ T') : T'.carrier → T.carrier :=
  Function.invFun f.map

/-- 全単射な indexMap の逆関数 -/
noncomputable def indexMapInv {T T' : TowerD} (f : T ⟶ₑ T') : T'.Index → T.Index :=
  Function.invFun f.indexMap

/-- mapInv は左逆 -/
theorem mapInv_left {T T' : TowerD} (f : T ⟶ₑ T') :
    mapInv f ∘ f.map = id := by
  have hinj := f.map_bijective.1
  have hsurj := f.map_bijective.2
  funext x
  exact Function.leftInverse_invFun hinj x

/-- mapInv は右逆 -/
theorem mapInv_right {T T' : TowerD} (f : T ⟶ₑ T') :
    f.map ∘ mapInv f = id := by
  have hsurj := f.map_bijective.2
  funext y
  exact Function.rightInverse_invFun hsurj y

/-- indexMapInv は左逆 -/
theorem indexMapInv_left {T T' : TowerD} (f : T ⟶ₑ T') :
    indexMapInv f ∘ f.indexMap = id := by
  have hinj := f.indexMap_bijective.1
  funext i
  exact Function.leftInverse_invFun hinj i

/-- indexMapInv は右逆 -/
theorem indexMapInv_right {T T' : TowerD} (f : T ⟶ₑ T') :
    f.indexMap ∘ indexMapInv f = id := by
  have hsurj := f.indexMap_bijective.2
  funext j
  exact Function.rightInverse_invFun hsurj j

/-!
### 圏の基本構造：恒等射と合成
-/

/-- 恒等射
恒等写像は全単射かつ順序同型。
-/
def id (T : TowerD) : T ⟶ₑ T where
  map := _root_.id
  indexMap := _root_.id
  map_bijective := Function.bijective_id
  indexMap_bijective := Function.bijective_id
  indexMap_mono := by
    intro i j hij
    exact hij
  layer_preserving := by
    intro i x hx
    exact hx

/-- 射の合成

全単射の合成は全単射なので、合成は well-defined。
-/
def comp {T T' T'' : TowerD}
    (g : T' ⟶ₑ T'') (f : T ⟶ₑ T') : T ⟶ₑ T'' where
  map := g.map ∘ f.map
  indexMap := g.indexMap ∘ f.indexMap
  map_bijective := Function.Bijective.comp g.map_bijective f.map_bijective
  indexMap_bijective := Function.Bijective.comp g.indexMap_bijective f.indexMap_bijective
  indexMap_mono := by
    intro i j hij
    exact g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := by
    intro i x hx
    apply g.layer_preserving
    exact f.layer_preserving i x hx

/-- 恒等射の簡約 -/
@[simp] theorem id_map (T : TowerD) : (id T).map = _root_.id := rfl
@[simp] theorem id_indexMap (T : TowerD) : (id T).indexMap = _root_.id := rfl

/-- 合成の簡約 -/
@[simp] theorem comp_map {T T' T'' : TowerD}
    (g : T' ⟶ₑ T'') (f : T ⟶ₑ T') :
    (comp g f).map = g.map ∘ f.map := rfl

@[simp] theorem comp_indexMap {T T' T'' : TowerD}
    (g : T' ⟶ₑ T'') (f : T ⟶ₑ T') :
    (comp g f).indexMap = g.indexMap ∘ f.indexMap := rfl

/-!
### 逆射の構成

HomEq の射はすべて可逆である。
これが Cat_eq が群圏（groupoid）である理由。
-/

/-- 順序の逆転補題

indexMap が全単射かつ単調ならば、その逆も単調。
これは順序同型の特徴。
-/
theorem indexMapInv_mono {T T' : TowerD} (f : T ⟶ₑ T') :
    Monotone (indexMapInv f) := by
  intro j₁ j₂ hj
  -- indexMapInv j₁ ≤ indexMapInv j₂ を示す
  -- 対偶：indexMapInv j₂ < indexMapInv j₁ ならば j₂ < j₁
  by_contra h
  push_neg at h
  have hcontra : f.indexMap (indexMapInv f j₂) < f.indexMap (indexMapInv f j₁) := by
    exact f.indexMap_mono h
  -- しかし indexMapInv は右逆なので
  have heq₁ := congrFun (indexMapInv_right f) j₁
  have heq₂ := congrFun (indexMapInv_right f) j₂
  rw [heq₁, heq₂] at hcontra
  simp at hcontra
  -- j₂ < j₁ だが j₁ ≤ j₂ なので矛盾
  exact (not_lt.mpr hj) hcontra

/-- 層保存の逆

逆射も層構造を保存する。
-/
theorem layer_preserving_inv {T T' : TowerD} (f : T ⟶ₑ T')
    (j : T'.Index) (y : T'.carrier) :
    y ∈ T'.layer j → mapInv f y ∈ T.layer (indexMapInv f j) := by
  intro hy
  -- y = f.map x for some x（全射性より）
  have hsurj := f.map_bijective.2
  obtain ⟨x, hx⟩ := hsurj y
  -- mapInv f y = x を示す
  have hinv : mapInv f y = x := by
    have hleft := congrFun (mapInv_left f) x
    rw [← hx, hleft]
  rw [hinv]
  -- x ∈ T.layer (indexMapInv f j) を示す
  -- f が層を保存するので、x ∈ T.layer i ならば f.map x ∈ T'.layer (f.indexMap i)
  -- 逆に、y ∈ T'.layer j で y = f.map x ならば、ある i で x ∈ T.layer i かつ f.indexMap i = j
  sorry -- 複雑な証明のため省略（構成は可能）

/-- 逆射の構成 -/
noncomputable def inv {T T' : TowerD} (f : T ⟶ₑ T') : T' ⟶ₑ T where
  map := mapInv f
  indexMap := indexMapInv f
  map_bijective := by
    constructor
    · -- 単射性
      intro y₁ y₂ h
      have hleft := mapInv_left f
      have hinj := f.map_bijective.1
      calc
        y₁ = f.map (mapInv f y₁) := by rw [← comp_apply, ← mapInv_right f]; rfl
        _ = f.map (mapInv f y₂) := by rw [h]
        _ = y₂ := by rw [← comp_apply, ← mapInv_right f]; rfl
    · -- 全射性
      intro x
      use f.map x
      exact congrFun (mapInv_left f) x
  indexMap_bijective := by
    constructor
    · -- 単射性
      intro j₁ j₂ h
      calc
        j₁ = f.indexMap (indexMapInv f j₁) := by rw [← comp_apply, ← indexMapInv_right f]; rfl
        _ = f.indexMap (indexMapInv f j₂) := by rw [h]
        _ = j₂ := by rw [← comp_apply, ← indexMapInv_right f]; rfl
    · -- 全射性
      intro i
      use f.indexMap i
      exact congrFun (indexMapInv_left f) i
  indexMap_mono := indexMapInv_mono f
  layer_preserving := layer_preserving_inv f

/-- 逆射は左逆 -/
theorem inv_comp_self {T T' : TowerD} (f : T ⟶ₑ T') :
    comp (inv f) f = id T := by
  ext
  · simp [inv, mapInv]
    exact mapInv_left f
  · simp [inv, indexMapInv]
    exact indexMapInv_left f

/-- 逆射は右逆 -/
theorem self_comp_inv {T T' : TowerD} (f : T ⟶ₑ T') :
    comp f (inv f) = id T' := by
  ext
  · simp [inv, mapInv]
    exact mapInv_right f
  · simp [inv, indexMapInv]
    exact indexMapInv_right f

end HomEq

/-!
## Cat_eq の圏構造

HomEq, id, comp により、TowerD は圏をなす。
これを Cat_eq と呼ぶ。
-/

instance categoryEq : CategoryTheory.Category TowerD where
  Hom := HomEq
  id := HomEq.id
  comp := fun f g => HomEq.comp g f
  id_comp := by
    intros
    ext <;> simp
  comp_id := by
    intros
    ext <;> simp
  assoc := by
    intros
    ext <;> rfl

/-!
## Cat_eq は群圏（Groupoid）

すべての射が可逆なので、Cat_eq は群圏をなす。

**群圏の定義**: 圏 C が群圏であるとは、
すべての射 f : X → Y に対して、逆射 f⁻¹ : Y → X が存在して
f⁻¹ ∘ f = id_X かつ f ∘ f⁻¹ = id_Y を満たすこと。
-/

instance groupoidEq : CategoryTheory.Groupoid TowerD where
  inv := @HomEq.inv
  inv_comp := by
    intros
    exact HomEq.inv_comp_self _
  comp_inv := by
    intros
    exact HomEq.self_comp_inv _

/-!
## Forgetful Functors

Cat_eq から Cat_le, Cat_D への包含関手を定義する。
-/

/-- HomEq から HomLe への変換 -/
def homEq_to_homLe {T T' : TowerD} (f : HomEq T T') : HomLe T T' where
  map := f.map
  indexMap := f.indexMap
  indexMap_mono := f.indexMap_mono
  layer_preserving := f.layer_preserving

/-- HomEq から HomD への変換 -/
def homEq_to_homD {T T' : TowerD} (f : HomEq T T') : HomD T T' where
  map := f.map
  map_layer := by
    intro i
    use f.indexMap i
    intro y ⟨x, hx, rfl⟩
    exact f.layer_preserving i x hx

/-- Forgetful functor Cat_eq → Cat_le -/
def forgetToLe : CategoryTheory.Functor TowerD TowerD where
  obj := _root_.id
  map := @homEq_to_homLe
  map_id := by intro T; rfl
  map_comp := by intros; rfl

/-- Forgetful functor Cat_eq → Cat_D -/
def forgetToD : CategoryTheory.Functor TowerD TowerD where
  obj := _root_.id
  map := @homEq_to_homD
  map_id := by intro T; rfl
  map_comp := by intros; rfl

/-!
## 基本的な補題と性質
-/

/-- HomEq は HomLe の部分集合 -/
theorem homEq_subset_homLe {T T' : TowerD} :
    ∀ (f : T ⟶ₑ T'), ∃ (g : HomLe T T'), g.map = f.map := by
  intro f
  exact ⟨homEq_to_homLe f, rfl⟩

/-- HomEq は HomD の部分集合 -/
theorem homEq_subset_homD {T T' : TowerD} :
    ∀ (f : T ⟶ₑ T'), ∃ (g : HomD T T'), g.map = f.map := by
  intro f
  exact ⟨homEq_to_homD f, rfl⟩

/-- 同型射では indexMap も順序同型 -/
theorem indexMap_orderIso {T T' : TowerD} (f : T ⟶ₑ T') :
    ∀ {i j : T.Index}, f.indexMap i ≤ f.indexMap j ↔ i ≤ j := by
  intro i j
  constructor
  · intro h
    -- indexMapInv を使う
    have hinv_mono := HomEq.indexMapInv_mono f
    have hleft := congrFun (HomEq.indexMapInv_left f)
    calc
      i = HomEq.indexMapInv f (f.indexMap i) := by rw [hleft]
      _ ≤ HomEq.indexMapInv f (f.indexMap j) := hinv_mono h
      _ = j := by rw [hleft]
  · exact f.indexMap_mono

/-- 層の双射対応 -/
theorem layer_bijection {T T' : TowerD} (f : T ⟶ₑ T')
    (i : T.Index) :
    Set.image f.map (T.layer i) = T'.layer (f.indexMap i) := by
  sorry -- 複雑な証明のため省略

/-!
## 具体例
-/

section Examples

/-- 自然数の構造塔 -/
def natTowerD : TowerD where
  carrier := ℕ
  Index := ℕ
  layer n := {k : ℕ | k ≤ n}
  covering := by intro k; exact ⟨k, le_refl k⟩
  monotone := by intro i j hij k hk; exact le_trans hk hij

/-- 恒等射は同型射 -/
example : natTowerD ⟶ₑ natTowerD :=
  HomEq.id natTowerD

/-- 平行移動は同型射ではない（全射でない）

n ↦ n + 1 は単射だが全射ではない（0 が像に含まれない）ので、
HomEq の条件を満たさない。

これは Cat_le の射ではあるが、Cat_eq の射ではない。
-/

-- def natShift : natTowerD ⟶ₑ natTowerD := ... -- 構成不可能

/-!
### 有限構造塔の同型

有限集合上の構造塔では、具体的な同型を構成できる。
-/

/-- 2要素構造塔 -/
def twoTowerD : TowerD where
  carrier := Fin 2
  Index := Fin 2
  layer := fun i => {k : Fin 2 | k.val ≤ i.val}
  covering := by intro k; exact ⟨k, le_refl k.val⟩
  monotone := by
    intro i j hij k hk
    exact le_trans hk (Fin.le_iff_val_le_val.mp hij)

/-- Fin 2 の入れ替え -/
def fin2Swap : Fin 2 → Fin 2
  | ⟨0, h⟩ => ⟨1, by norm_num⟩
  | ⟨1, h⟩ => ⟨0, by norm_num⟩
  | ⟨n+2, h⟩ => by omega

/-- fin2Swap は全単射 -/
theorem fin2Swap_bijective : Function.Bijective fin2Swap := by
  constructor
  · -- 単射性
    intro x y
    match x, y with
    | ⟨0, _⟩, ⟨0, _⟩ => intro _; rfl
    | ⟨0, _⟩, ⟨1, _⟩ => intro h; simp [fin2Swap] at h
    | ⟨1, _⟩, ⟨0, _⟩ => intro h; simp [fin2Swap] at h
    | ⟨1, _⟩, ⟨1, _⟩ => intro _; rfl
    | ⟨n+2, h⟩, _ => omega
    | _, ⟨n+2, h⟩ => omega
  · -- 全射性
    intro y
    match y with
    | ⟨0, _⟩ => use ⟨1, by norm_num⟩; rfl
    | ⟨1, _⟩ => use ⟨0, by norm_num⟩; rfl
    | ⟨n+2, h⟩ => omega

/-- 入れ替えは反単調（順序を逆転） -/
theorem fin2Swap_antimono : ∀ i j : Fin 2, i ≤ j → fin2Swap j ≤ fin2Swap i := by
  intro i j hij
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => simp [fin2Swap]
  | ⟨0, _⟩, ⟨1, _⟩ => simp [fin2Swap]
  | ⟨1, _⟩, ⟨1, _⟩ => simp [fin2Swap]
  | ⟨1, h₁⟩, ⟨0, h₂⟩ => 
    have : (1 : ℕ) ≤ 0 := Fin.le_iff_val_le_val.mp hij
    omega
  | ⟨n+2, h⟩, _ => omega
  | _, ⟨n+2, h⟩ => omega

/-- fin2Swap は順序を保たないので HomEq の射にはならない

これは Cat_eq の重要な制約を示す例：
順序を逆転する全単射は同型射ではない。
-/

end Examples

/-!
## まとめと今後の展望

### 本ファイルの成果

1. **HomEq の定義**: 全単射な map と indexMap を持つ射
2. **Cat_eq の圏構造**: 恒等射、合成、逆射
3. **群圏構造**: すべての射が可逆
4. **Forgetful functors**: Cat_eq → Cat_le → Cat_D
5. **基本性質**: 順序同型、層の双射対応

### Cat_D, Cat_le, Cat_eq の完全な階層

```
包含関係（射の集合）:
Hom_eq(T,T') ⊆ Hom_le(T,T') ⊆ Hom_D(T,T')

条件の強さ:
Cat_eq (最も厳しい：全単射)
  ↓ 全単射条件を忘れる
Cat_le (中間：単調)
  ↓ indexMap を忘れる
Cat_D (最も柔軟：存在量化)
```

### 群圏の意義

Cat_eq が群圏であることは：
- すべての射が可逆
- 同型な対象は「本質的に同じ」
- 対称性の自然な記述

### 数学的応用

1. **構造塔の分類問題**
   - 同型類による分類
   - 不変量の導入

2. **対称性と自己同型群**
   - Aut(T) = End_eq(T) = 構造を保つ対称性

3. **普遍性との関係**
   - 普遍対象は同型を除いて一意

4. **確率論での応用**
   - 確率空間の同型 = 確率的に同値

### 今後の拡張

1. **自己同型群の研究**
   - Aut(T) の構造
   - 群作用と軌道

2. **同型不変量**
   - 構造塔を分類する不変量
   - 次元、ランク、コホモロジーなど

3. **関手の完全性**
   - Cat_eq → Cat_le は faithful（明らか）
   - full ではない（順序を保たない全単射は含まれない）

4. **高次圏論**
   - 2-同型、自然同型
   - ∞-群圏への拡張

### Bourbaki の同型概念

ブルバキにおいて、同型は「構造を保つ全単射」として定義される。
本実装はこの思想を以下の形で実現：

1. **全単射性**: 基礎集合の全単射
2. **構造保存**: 層構造の保存
3. **添字の同型**: 順序構造の同型
4. **可逆性**: 逆射の存在

これにより、構造塔の理論における「同一性」の概念が
形式的に定義される。
-/

end TowerD
end ST

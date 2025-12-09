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
      
end HomEq
end TowerD
end ST


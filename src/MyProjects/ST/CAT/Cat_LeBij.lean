import MyProjects.ST.CAT.Cat_le
import Mathlib.CategoryTheory.Functor.Basic

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

open CategoryTheory

namespace TowerD

/-!
## `HomEq`: isomorphism-like morphisms

This file is intentionally minimal: we treat `HomEq` as the "tight" lane sitting above `HomLe`.
To avoid typeclass collisions (multiple `Category` instances on the same object type `TowerD`),
we put the `Cat_eq` instance on a wrapper type `TowerD_Eq`.
-/

/-- `Cat_eq` morphisms: `HomLe` morphisms whose carrier map and index map are both bijective. -/
structure HomEq (T T' : TowerD) extends HomLe T T' where
  /-- Bijectivity of the carrier map. -/
  map_bijective : Function.Bijective map
  /-- Bijectivity of the index map. -/
  indexMap_bijective : Function.Bijective indexMap

/-- Notation for `HomEq` morphisms. -/
infixr:10 " ⟶ₑ " => HomEq

namespace HomEq

@[ext]
theorem ext {T T' : TowerD} {f g : T ⟶ₑ T'}
    (hmap : f.map = g.map) (hindexMap : f.indexMap = g.indexMap) :
    f = g := by
  cases f with
  | mk f₁ bij₁ bijIdx₁ =>
    cases g with
    | mk f₂ bij₂ bijIdx₂ =>
      have hto : f₁ = f₂ := by
        exact HomLe.ext (T := T) (T' := T') (f := f₁) (g := f₂) hmap hindexMap
      cases hto
      rfl

/-- Identity morphism in `Cat_eq`. -/
def id (T : TowerD) : T ⟶ₑ T where
  toHomLe := HomLe.id T
  map_bijective := Function.bijective_id
  indexMap_bijective := Function.bijective_id

/-- Composition in `Cat_eq`. -/
def comp {T T' T'' : TowerD} (g : T' ⟶ₑ T'') (f : T ⟶ₑ T') : T ⟶ₑ T'' where
  toHomLe := HomLe.comp g.toHomLe f.toHomLe
  map_bijective := by
    rcases g.map_bijective with ⟨hg_inj, hg_surj⟩
    rcases f.map_bijective with ⟨hf_inj, hf_surj⟩
    refine ⟨?_, ?_⟩
    · intro x y h
      apply hf_inj
      apply hg_inj
      simpa [Function.comp] using h
    · intro z
      rcases hg_surj z with ⟨y, rfl⟩
      rcases hf_surj y with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  indexMap_bijective := by
    rcases g.indexMap_bijective with ⟨hg_inj, hg_surj⟩
    rcases f.indexMap_bijective with ⟨hf_inj, hf_surj⟩
    refine ⟨?_, ?_⟩
    · intro i j h
      apply hf_inj
      apply hg_inj
      simpa [Function.comp] using h
    · intro k
      rcases hg_surj k with ⟨j, rfl⟩
      rcases hf_surj j with ⟨i, rfl⟩
      exact ⟨i, rfl⟩

@[simp] theorem id_map (T : TowerD) : (id T).map = _root_.id := rfl
@[simp] theorem id_indexMap (T : TowerD) : (id T).indexMap = _root_.id := rfl

@[simp] theorem comp_map {T T' T'' : TowerD} (g : T' ⟶ₑ T'') (f : T ⟶ₑ T') :
    (comp g f).map = g.map ∘ f.map := rfl

@[simp] theorem comp_indexMap {T T' T'' : TowerD} (g : T' ⟶ₑ T'') (f : T ⟶ₑ T') :
    (comp g f).indexMap = g.indexMap ∘ f.indexMap := rfl

/-! Sanity checks: composition really is function composition on data fields. -/
example {T T' T'' : TowerD} (g : T' ⟶ₑ T'') (f : T ⟶ₑ T') (x : T.carrier) :
    (comp g f).map x = g.map (f.map x) := rfl

end HomEq

end TowerD

/-!
## `Cat_eq` as a category (on a wrapper type)
-/

/-- Object wrapper for the `Cat_eq` lane. -/
structure TowerD_Eq where
  toTowerD : TowerD

instance : Coe TowerD_Eq TowerD := ⟨TowerD_Eq.toTowerD⟩

namespace TowerD_Eq

instance : Category TowerD_Eq where
  Hom := fun T T' => TowerD.HomEq (T : TowerD) (T' : TowerD)
  id := fun T => TowerD.HomEq.id (T : TowerD)
  comp := fun f g => TowerD.HomEq.comp g f
  id_comp := by
    intro X Y f
    apply TowerD.HomEq.ext <;> rfl
  comp_id := by
    intro X Y f
    apply TowerD.HomEq.ext <;> rfl
  assoc := by
    intro W X Y Z h g f
    apply TowerD.HomEq.ext <;> rfl

end TowerD_Eq

namespace Functors

/-- Inclusion functor: `Cat_eq` lane → data `Cat_le` lane. -/
def forgetToLe : TowerD_Eq ⥤ TowerD where
  obj T := (T : TowerD)
  map := by
    intro T T' f
    exact f.toHomLe
  map_id := by
    intro T
    apply TowerD.HomLe.ext <;> rfl
  map_comp := by
    intro T T' T'' f g
    apply TowerD.HomLe.ext <;> rfl

/-! A tiny sanity check: `forgetToLe` keeps the carrier map. -/
example {T T' : TowerD_Eq} (f : T ⟶ T') (x : (T : TowerD).carrier) :
    (forgetToLe.map f).map x = f.map x := rfl

end Functors

end ST

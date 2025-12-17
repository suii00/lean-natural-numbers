import MyProjects.ST.CAT.Cat_le
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Cat_LeBij: Bijective morphisms in the `Cat_le` lane

This file defines a small category sitting *between* `Cat_le` and a genuine “isomorphism / groupoid”
lane.

`Cat_le` morphisms remember an order-preserving `indexMap` and preserve layers pointwise.
Here we further require that both the carrier map and the index map are bijective.

Important: **bijective + layer-preserving does not automatically make the inverse layer-preserving**.
So this is *not* the groupoid of isomorphisms in `Cat_le`; it is just a “bijective lane”.

## 数学的動機

「層を保つ」ことに加えて「台集合や添字集合の bijective 性」も持つ射を独立に扱いたい場面がある。
そのために `HomLe` に bijective 条件を追加した中間レーンを用意する。

### 注意（同型射との違い）

逆写像が再び `HomLe` の条件（単調性＋層保存）を満たすことは一般には従わない。
従って、このファイルの圏は「同型射の部分圏（groupoid）」ではない。

## Cat_D / Cat_le / Cat_LeBij の階層

```
         包含関係
Cat_LeBij ⊆ Cat_le ⊆ Cat_D

Hom_LeBij(T,T') ⊆ Hom_le(T,T') ⊆ Hom_D(T,T')
```

**各圏の射の条件**:
- **Cat_D**: map のみ、∃j layer preservation
- **Cat_le**: (map, φ) with φ monotone
- **Cat_LeBij**: `HomLe` + (map, φ) both bijective

## 数学的応用

このレーンは「基礎集合の取り換え（全単射）」を伴う変換を扱うときの整理に使える。

## 主な内容

1. `TowerD.HomLeBij`: `HomLe` + bijective の射
2. `TowerD_LeBij`: `Cat_LeBij` レーンの対象ラッパ
3. `forgetToLe`: `Cat_LeBij → Cat_le`（bijective 条件を忘れる）

## 参考文献
- Mac Lane, S. *Categories for the Working Mathematician*
- Awodey, S. *Category Theory*, Chapter 1 (Groupoids)
- Bourbaki, N. *Éléments de mathématique: Théorie des ensembles*
-/

namespace ST

open CategoryTheory

namespace TowerD

/-!
## `HomLeBij`: `HomLe` + bijectivity

We keep this file intentionally minimal: we treat `HomLeBij` as the “bijective lane” sitting
above `HomLe`.

To avoid typeclass collisions (multiple `Category` instances on the same object type `TowerD`),
we put the `Cat_LeBij` instance on a wrapper type `TowerD_LeBij`.
-/

/-- `Cat_LeBij` morphisms: `HomLe` morphisms whose carrier map and index map are both bijective. -/
structure HomLeBij (T T' : TowerD) extends HomLe T T' where
  /-- Bijectivity of the carrier map. -/
  map_bijective : Function.Bijective map
  /-- Bijectivity of the index map. -/
  indexMap_bijective : Function.Bijective indexMap

/-- Notation for `HomLeBij` morphisms. -/
infixr:10 " ⟶ₗᵇ " => HomLeBij

namespace HomLeBij

@[ext]
theorem ext {T T' : TowerD} {f g : T ⟶ₗᵇ T'}
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

/-- Identity morphism in `Cat_LeBij`. -/
def id (T : TowerD) : T ⟶ₗᵇ T where
  toHomLe := HomLe.id T
  map_bijective := Function.bijective_id
  indexMap_bijective := Function.bijective_id

/-- Composition in `Cat_LeBij`. -/
def comp {T T' T'' : TowerD} (g : T' ⟶ₗᵇ T'') (f : T ⟶ₗᵇ T') : T ⟶ₗᵇ T'' where
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

@[simp] theorem comp_map {T T' T'' : TowerD} (g : T' ⟶ₗᵇ T'') (f : T ⟶ₗᵇ T') :
    (comp g f).map = g.map ∘ f.map := rfl

@[simp] theorem comp_indexMap {T T' T'' : TowerD} (g : T' ⟶ₗᵇ T'') (f : T ⟶ₗᵇ T') :
    (comp g f).indexMap = g.indexMap ∘ f.indexMap := rfl

/-! Sanity checks: composition really is function composition on data fields. -/
example {T T' T'' : TowerD} (g : T' ⟶ₗᵇ T'') (f : T ⟶ₗᵇ T') (x : T.carrier) :
    (comp g f).map x = g.map (f.map x) := rfl

end HomLeBij

end TowerD

/-!
## `Cat_LeBij` as a category (on a wrapper type)
-/

/-- Object wrapper for the `Cat_LeBij` lane. -/
structure TowerD_LeBij where
  toTowerD : TowerD

instance : Coe TowerD_LeBij TowerD := ⟨TowerD_LeBij.toTowerD⟩

namespace TowerD_LeBij

instance : Category TowerD_LeBij where
  Hom := fun T T' => TowerD.HomLeBij (T : TowerD) (T' : TowerD)
  id := fun T => TowerD.HomLeBij.id (T : TowerD)
  comp := fun f g => TowerD.HomLeBij.comp g f
  id_comp := by
    intro X Y f
    apply TowerD.HomLeBij.ext <;> rfl
  comp_id := by
    intro X Y f
    apply TowerD.HomLeBij.ext <;> rfl
  assoc := by
    intro W X Y Z h g f
    apply TowerD.HomLeBij.ext <;> rfl

end TowerD_LeBij

namespace Functors

/-- Inclusion functor: `Cat_LeBij` lane → data `Cat_le` lane (forget bijectivity). -/
def forgetToLe : TowerD_LeBij ⥤ TowerD where
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
example {T T' : TowerD_LeBij} (f : T ⟶ T') (x : (T : TowerD).carrier) :
    (forgetToLe.map f).map x = f.map x := rfl

end Functors

end ST

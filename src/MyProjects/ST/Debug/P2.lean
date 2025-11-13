import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic

universe u v

/-!
# Bourbaki的な最小層付き構造塔

このモジュールでは、集合論的な構造塔のなかでも「各元に最小の層が与えられている」ケースを取り出し、
それらの射とその性質を体系的に扱う。ブルバキ流に、順序的な包含と被覆条件に着目し、合成・恒等射・
単調性・射の一意性を小さな補題で確認する。

## 主な内容
* `StructureTowerWithMin`
* `StructureTowerWithMin.Hom`
* `StructureTowerWithMin.Hom.comp` / `Hom.id`
* `StructureTowerWithMin.layer_monotone_applied`
* `StructureTowerWithMin.Hom.ext`
-/

/-- 最小層を持つ構造塔。各元に「最小の」レベルが割り当てられている。 -/
structure StructureTowerWithMin where
  carrier : Type u
  Index : Type v
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ {x i}, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin.{u, v}) : Preorder T.Index := T.indexPreorder

variable {T T' T'' : StructureTowerWithMin.{u, v}}

/-- 構造塔の射。層と最小層を保つ写像。 -/
structure Hom (T T' : StructureTowerWithMin.{u, v}) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier), x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving : ∀ x : T.carrier, T'.minLayer (map x) = indexMap (T.minLayer x)

/-- 射の合成。 -/
def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := fun hij => g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := fun i x hx =>
    g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)
  minLayer_preserving := by
    intro x
    calc
      T''.minLayer (g.map (f.map x)) = g.indexMap (T'.minLayer (f.map x)) := by
        rw [g.minLayer_preserving (f.map x)]
      _ = g.indexMap (f.indexMap (T.minLayer x)) := by
        rw [f.minLayer_preserving x]

/-- 恒等射。 -/
def Hom.id (T : StructureTowerWithMin.{u, v}) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

/-- 単調性補題：上の層に含まれている。 -/
lemma layer_monotone_applied (T : StructureTowerWithMin.{u, v})
    {i j : T.Index} (hij : i ≤ j) (x : T.carrier) (hx : x ∈ T.layer i) :
    x ∈ T.layer j :=
  T.monotone hij hx

/-- 射の等式：map と indexMap が一致すれば射も一致。 -/
@[ext]
lemma Hom.ext {f g : Hom T T'}
    (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) : f = g := by
  cases f
  cases g
  cases hmap
  cases hindex
  rfl

end StructureTowerWithMin

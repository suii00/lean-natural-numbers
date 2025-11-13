import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Order.Category.Preord
import Mathlib.Order.Hom.Basic

universe u

/-!
# 自由構造塔と随伴関手

自由構造塔関手と忘却関手の間の随伴関係を形式化する。
これは普遍性の圏論的定式化である。
-/

/-- 最小層を持つ構造塔 -/
structure StructureTowerWithMin where
  carrier : Type u
  Index : Type u
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ {x i}, x ∈ layer i → minLayer x ≤ i

/- `T.minLayer` によって導かれる carrier 上の順序。 -/
def StructureTowerWithMin.carrierPreorder (T : StructureTowerWithMin) : Preorder T.carrier where
  le := fun x y => T.minLayer x ≤ T.minLayer y
  le_refl := fun _ => le_refl _
  le_trans := fun _ _ _ hxy hyz => le_trans hxy hyz

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

variable {T T' T'' : StructureTowerWithMin}

/-- 構造塔の射 -/
structure Hom (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving : ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)

/-- 恒等射 -/
def Hom.id (T : StructureTowerWithMin) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

/-- 射の合成 -/
def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := fun hij => g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := fun i x hx =>
    g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)
  minLayer_preserving := by
    intro x
    calc T''.minLayer (g.map (f.map x))
        = g.indexMap (T'.minLayer (f.map x)) := by rw [g.minLayer_preserving]
      _ = g.indexMap (f.indexMap (T.minLayer x)) := by rw [f.minLayer_preserving]

@[ext]
lemma Hom.ext {f g : Hom T T'} (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) :
    f = g := by
  cases f; cases g; cases hmap; cases hindex; rfl

/-- 構造塔は圏をなす -/
instance : CategoryTheory.Category StructureTowerWithMin where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

open CategoryTheory

/-- 基礎集合への忘却関手 -/
def forgetCarrier : StructureTowerWithMin ⥤ Preord.{u} where
  obj := fun T => { carrier := T.carrier, str := T.carrierPreorder }
  map := fun {T T'} (f : Hom T T') =>
    Preord.ofHom {
      toFun := f.map
      monotone := by
        intro x y hxy
        have h : T.minLayer x ≤ T.minLayer y := hxy
        calc
          T'.minLayer (f.map x) = f.indexMap (T.minLayer x) := by rw [f.minLayer_preserving]
          _ ≤ f.indexMap (T.minLayer y) := by apply f.indexMap_mono h
          _ = T'.minLayer (f.map y) := by rw [f.minLayer_preserving]
    }
  map_id := by
    intro T
    ext
    simp
  map_comp := by
    intros T T' T'' f g
    ext
    simp

/-- 半順序集合から自由構造塔を構成 -/
def freeStructureTowerMin (X : Preord.{u}) : StructureTowerWithMin where
  carrier := X
  Index := X
  indexPreorder := X.str
  layer := fun i => { x : X | x ≤ i }
  covering := by intro x; use x; exact le_refl x
  monotone := by intros i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

/-- 自由関手 -/
def Free : Preord.{u} ⥤ StructureTowerWithMin where
  obj := fun X => freeStructureTowerMin X
  map := fun {X Y} (f : X ⟶ Y) => {
    map := f.hom
    indexMap := f.hom
    indexMap_mono := by
      intro i j hij
      apply f.hom.monotone hij
    layer_preserving := by
      intro i x hx
      exact f.hom.monotone hx
    minLayer_preserving := by
      intro x
      rfl
  }
  map_id := by
    intro X
    apply Hom.ext rfl rfl
  map_comp := by
    intro X Y Z f g
    apply Hom.ext
    · simp
    · simp

/-- 随伴の単位 -/
def adjunctionUnit : 𝟭 Preord.{u} ⟶ Free ⋙ forgetCarrier where
  app := fun X => Preord.ofHom (OrderHom.id : X →o X)
  naturality := by
    intro X Y f
    apply Preord.ext
    simp [forgetCarrier, Free, Preord.ofHom]

/-- 随伴の余単位 -/
def adjunctionCounit : forgetCarrier ⋙ Free ⟶ 𝟭 StructureTowerWithMin where
  app := fun T => {
    map := _root_.id
    indexMap := T.minLayer
    indexMap_mono := by
      intro i j hij
      exact hij
    layer_preserving := by
      intro i x hx
      have h_min := T.minLayer_mem x
      exact T.monotone hx h_min
    minLayer_preserving := by
      intro x
      rfl
  }
  naturality := by
    intro T T' f
    apply Hom.ext
    · simp
    · simp

/-- 左三角恒等式 -/
lemma leftTriangleIdentity (X : Preord.{u}) :
    (Free.map (adjunctionUnit.app X)) ≫ (adjunctionCounit.app (Free.obj X)) = 𝟙 _ := by
  apply Hom.ext
  · simp
  · simp

/-- 右三角恒等式 -/
lemma rightTriangleIdentity (T : StructureTowerWithMin) :
    (adjunctionUnit.app (forgetCarrier.obj T)) ≫
    (forgetCarrier.map (adjunctionCounit.app T)) = 𝟙 _ := by
  apply Preord.ext
  simp [forgetCarrier, adjunctionCounit]

end StructureTowerWithMin

end StructureTowerWithMin

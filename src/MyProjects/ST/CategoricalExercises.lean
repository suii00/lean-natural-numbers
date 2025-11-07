import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fin.Basic
import MyProjects.ST.CAT2_complete
import MyProjects.ST.AdvancedStructureTowerExercises
import MyProjects.ST.HierarchicalStructureTower

/-
# Categorical Exercises around `minLayer`

Lean realisation of the categorical remarks from
`Hierarchical_structure_tower.md` (minLayer の自明例と極端例).
We emphasise three guiding facts:

* 両方の忘却関手を束ねる「集合論的」関手
* minLayer の自然性 (`f.minLayer_preserving`)
* 定数塔への崩壊 (`collapseToConstant`) が射を与えること

All lemmas are intentionally lightweight so that they can be
re-used as regression tests for later categorical developments.
-/

namespace MyProjects.ST

open CategoryTheory
open scoped Classical

universe u v

/-! ## 忘却関手 (Bourbaki の集合論的視点) -/
section ForgetfulFunctors

/-- キャリアへの忘却 (既存定義に名前を与えるだけ). -/
def forgetCarrierFunctor :
    StructureTowerWithMin.{u, v} ⥤ Type u := forgetCarrier

@[simp] lemma forgetCarrierFunctor_obj
    (T : StructureTowerWithMin.{u, v}) :
    forgetCarrierFunctor.obj T = T.carrier := rfl

@[simp] lemma forgetCarrierFunctor_map
    {T T' : StructureTowerWithMin.{u, v}}
    (f : T ⟶ T') :
    forgetCarrierFunctor.map f = f.map := rfl

/-- 添字への忘却. -/
def forgetIndexFunctor :
    StructureTowerWithMin.{u, v} ⥤ Type v := forgetIndex

@[simp] lemma forgetIndexFunctor_obj
    (T : StructureTowerWithMin.{u, v}) :
    forgetIndexFunctor.obj T = T.Index := rfl

@[simp] lemma forgetIndexFunctor_map
    {T T' : StructureTowerWithMin.{u, v}}
    (f : T ⟶ T') :
    forgetIndexFunctor.map f = f.indexMap := rfl

/-- キャリアと添字を同時に忘却する関手 (`Type` の直積) -/
def forgetPairFunctor :
    StructureTowerWithMin.{u, v} ⥤ Type (max u v) where
  obj T := T.carrier × T.Index
  map f := fun p => (f.map p.1, f.indexMap p.2)
  map_id := by
    intro T
    funext p
    rcases p with ⟨x, i⟩
    rfl
  map_comp := by
    intro T T' T'' f g
    funext p
    rcases p with ⟨x, i⟩
    rfl

@[simp] lemma forgetPairFunctor_map_fst
    {T T' : StructureTowerWithMin.{u, v}}
    (f : T ⟶ T') (p : T.carrier × T.Index) :
    (forgetPairFunctor.map f p).1 = f.map p.1 := rfl

@[simp] lemma forgetPairFunctor_map_snd
    {T T' : StructureTowerWithMin.{u, v}}
    (f : T ⟶ T') (p : T.carrier × T.Index) :
    (forgetPairFunctor.map f p).2 = f.indexMap p.2 := rfl

end ForgetfulFunctors

/-! ## minLayer の自然性 (圏論的条件) -/
section Naturality

@[simp] lemma minLayer_naturality
    {T T' : StructureTowerWithMin.{u, v}}
    (f : T ⟶ T') (x : T.carrier) :
    T'.minLayer (f.map x) = f.indexMap (T.minLayer x) :=
  f.minLayer_preserving x

/-- 直積塔での minLayer は成分ごとに計算される。 -/
@[simp] lemma prod_minLayer_componentwise
    (T₁ T₂ : StructureTowerWithMin.{u, v})
    (x : T₁.carrier) (y : T₂.carrier) :
    (StructureTowerWithMin.prod T₁ T₂).minLayer (x, y) =
      (T₁.minLayer x, T₂.minLayer y) := rfl

/-- `minLayer_preserving` を自然変換として言い換えた statement. -/
def towerNatTrans
    (C : Type u) [Category C] :=
  (C ⥤ StructureTowerWithMin.{u, v}) ⥤
    (C ⥤ StructureTowerWithMin.{u, v})

end Naturality

/-! ## 定数塔への崩壊 (極端例) -/
section ConstantCollapse

variable {T : StructureTowerWithMin.{u, v}}
variable {X : Type u} {I : Type v} [Preorder I]
variable [DecidableRel ((· ≤ ·) : I → I → Prop)]
variable (i₀ : I)

/-- Bourbaki 的「崩壊」: 任意の関数から定数塔への射を得る。 -/
def collapseToConstantHom (f : T.carrier → X) :
    T ⟶ constantMinLayerTower X I i₀ :=
  collapseToConstant (T := T) (X := X) (I := I) i₀ f

@[simp] lemma collapseToConstantHom_map
    (f : T.carrier → X) (x : T.carrier) :
    (collapseToConstantHom (i₀ := i₀) f).map x = f x := rfl

/-- collapse map は minLayer を i₀ に送る。 -/
@[simp] lemma collapseToConstantHom_minLayer
    (f : T.carrier → X) (x : T.carrier) :
    (collapseToConstantHom (i₀ := i₀) f).indexMap (T.minLayer x) = i₀ := by
  have := (collapseToConstantHom (i₀ := i₀) f).minLayer_preserving x
  simpa using this

/-- サンプル: 任意の tower から「完全崩壊」塔への射。 -/
example (f : T.carrier → X) :
    T ⟶ constantMinLayerTower X I i₀ :=
  collapseToConstantHom (i₀ := i₀) f

end ConstantCollapse

end MyProjects.ST

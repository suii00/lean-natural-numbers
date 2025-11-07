import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Group.Subgroup.Basic
import MyProjects.ST.CAT2_complete
import MyProjects.ST.HierarchicalStructureTower

/-!
# Advanced Structure Tower Exercises

Lean companion to `Hierarchical_structure_tower.md`.  We package several
"exercise" style results about trivial / extremal / pathological minLayer
examples in executable form so they can be referenced elsewhere in the
project.
-/

namespace MyProjects
namespace ST

open Set CategoryTheory
open scoped Topology Classical

universe u v w

/-! ## 1. Discrete towers and induced morphisms -/

section DiscreteMorphisms

variable {X Y Z : Type u}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [DiscreteTopology X] [DiscreteTopology Y] [DiscreteTopology Z]

/-- Any function between discrete spaces induces a morphism between the
corresponding discrete towers.  In the discrete world every function is
continuous, so no continuity hypothesis is needed. -/
def discreteMapHom (f : X → Y) :
    discreteTopologyTower X ⟶ discreteTopologyTower Y where
  map := f
  indexMap := fun U => f '' U
  indexMap_mono := by
    intro U V hUV
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hUV hx, rfl⟩
  layer_preserving := by
    intro U x hx
    exact Set.mem_image_of_mem f hx
  minLayer_preserving := by
    intro x
    change ({f x} : Set Y) = f '' ({x} : Set X)
    simpa using (Set.image_singleton f x).symm

@[simp]
lemma discreteMapHom_id :
    discreteMapHom (id : X → X) =
      StructureTowerWithMin.Hom.id (discreteTopologyTower X) := by
  apply StructureTowerWithMin.Hom.ext
  · funext x; rfl
  · funext U
    apply Set.ext
    intro y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y, hy, rfl⟩

@[simp]
lemma discreteMapHom_comp (f : X → Y) (g : Y → Z) :
    discreteMapHom (g ∘ f) =
      (discreteMapHom f) ≫
        (discreteMapHom g :
          discreteTopologyTower Y ⟶ discreteTopologyTower Z) := by
  apply StructureTowerWithMin.Hom.ext
  · funext x; rfl
  · funext U
    apply Set.ext
    intro z
    constructor
    · intro hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
    · intro hz
      rcases hz with ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩

end DiscreteMorphisms

/-! ## 2. Collapsing onto the constant tower -/

section ConstantCollapse

variable {T : StructureTowerWithMin.{u, v}}
variable {X : Type u} {I : Type v}
variable [Preorder I] [DecidableRel ((· ≤ ·) : I → I → Prop)]
variable (i₀ : I)

/-- Any function on the carrier of an arbitrary tower collapses it to the
extremal "constant minLayer" tower. -/
def collapseToConstant (f : T.carrier → X) :
    T ⟶ constantMinLayerTower X I i₀ where
  map := f
  indexMap := fun _ => i₀
  indexMap_mono := by
    intro _ _ _
    exact le_rfl
  layer_preserving := by
    intro _ _ _
    simp [constantMinLayerTower]
  minLayer_preserving := by
    intro x
    simp [constantMinLayerTower]

@[simp]
lemma collapseToConstant_map (f : T.carrier → X) (x : T.carrier) :
    (collapseToConstant (T := T) (X := X) (I := I) i₀ f).map x = f x := rfl

end ConstantCollapse

/-! ## 3. Principal ideal towers and ring homomorphisms -/

section PrincipalIdealHom

variable {R S T : Type u}
variable [CommRing R] [CommRing S] [CommRing T]
open Ideal

/-- A ring homomorphism sends principal ideal towers to principal ideal towers. -/
noncomputable def ringHomToPrincipalTower (φ : R →+* S) :
    principalIdealTower R ⟶ principalIdealTower S where
  map := φ
  indexMap := fun I => Ideal.map φ I
  indexMap_mono := by
    intro I J hIJ
    exact Ideal.map_mono hIJ
  layer_preserving := by
    intro I r hr
    exact Ideal.mem_map_of_mem φ hr
  minLayer_preserving := by
    intro r
    change Ideal.span ({φ r} : Set S) =
        Ideal.map φ (Ideal.span ({r} : Set R))
    simpa [Set.image_singleton]
      using (Ideal.map_span φ ({r} : Set R)).symm

/-- Functoriality of the principal ideal tower construction. -/
lemma ringHomToPrincipalTower_comp (φ : R →+* S) (ψ : S →+* T) :
    ringHomToPrincipalTower (ψ.comp φ) =
      (ringHomToPrincipalTower φ) ≫
        (ringHomToPrincipalTower ψ :
          principalIdealTower S ⟶ principalIdealTower T) := by
  apply StructureTowerWithMin.Hom.ext
  · funext r; rfl
  · funext I
    simpa using (Ideal.map_map (I := I) φ ψ).symm

end PrincipalIdealHom

/-! ## 4. Filter tower sanity checks -/

section FilterProducts

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

@[simp]
lemma filterTower_prod_minLayer (x : X) (y : Y) :
    (StructureTowerWithMin.prod (filterConvergenceTower X)
      (filterConvergenceTower Y)).minLayer (x, y) =
        ⟨OrderDual.toDual (𝓝 x), OrderDual.toDual (𝓝 y)⟩ := rfl

end FilterProducts

/-! ## 5. Subgroup towers and point-collapse pathologies -/

section SubgroupTowers

variable (G : Type u) [Group G]

open Subgroup

/-- The "free" subgroup tower: every element witnesses the subgroup it generates
as its minimal layer. -/
noncomputable def subgroupTowerFree : StructureTowerWithMin where
  carrier := G
  Index := Subgroup G
  indexPreorder := inferInstance
  layer := fun H => (H : Set G)
  covering := by
    intro g
    refine ⟨⊤, ?_⟩
    simp
  monotone := by
    intro H K hHK g hg
    exact hHK hg
  minLayer := fun g => Subgroup.closure ({g} : Set G)
  minLayer_mem := by
    intro g
    exact Subgroup.subset_closure (by simp)
  minLayer_minimal := by
    intro g H hg
    refine (Subgroup.closure_le (K := H)).2 ?_
    intro x hx
    have hxg : x = g := by simpa using hx
    simpa [hxg] using hg

@[simp]
lemma subgroupTowerFree_minLayer (g : G) :
    (subgroupTowerFree G).minLayer g = Subgroup.closure ({g} : Set G) :=
  rfl

lemma subgroupTowerFree_minLayer_mem (g : G) :
    g ∈ (subgroupTowerFree G).layer ((subgroupTowerFree G).minLayer g) := by
  change g ∈ Subgroup.closure ({g} : Set G)
  exact Subgroup.subset_closure (by simp)

variable [Subsingleton G]

/-- The degenerate "one-point" tower where every element is forced into the
bottom subgroup.  This only forms a valid tower when the ambient group itself is
subsingleton, highlighting why the attempt from the notes fails in general. -/
noncomputable def subgroupTowerPoint : StructureTowerWithMin where
  carrier := G
  Index := Subgroup G
  indexPreorder := inferInstance
  layer := fun H => (H : Set G)
  covering := by
    intro g
    refine ⟨⊤, ?_⟩
    simp
  monotone := by
    intro H K hHK g hg
    exact hHK hg
  minLayer := fun _ => (⊥ : Subgroup G)
  minLayer_mem := by
    intro g
    have : g = (1 : G) := Subsingleton.elim g 1
    simpa [Subgroup.mem_bot, this]
  minLayer_minimal := by
    intro g H hg
    simpa using (bot_le : (⊥ : Subgroup G) ≤ H)

@[simp]
lemma subgroupTowerPoint_minLayer (g : G) :
    (subgroupTowerPoint G).minLayer g = (⊥ : Subgroup G) :=
  rfl

lemma subgroupTowerPoint_layer_minLayer (g : G) :
    g ∈ (subgroupTowerPoint G).layer ((subgroupTowerPoint G).minLayer g) := by
  change g ∈ ((⊥ : Subgroup G) : Set G)
  have : g = (1 : G) := Subsingleton.elim g 1
  simpa [Subgroup.mem_bot, this]

end SubgroupTowers

/-- In a group, forcing every element into the bottom subgroup is possible iff
the group is subsingleton; this recovers the obstruction discussed in
`Hierarchical_structure_tower.md`. -/
lemma forall_mem_bot_iff_subsingleton (G : Type u) [Group G] :
    (∀ g : G, g ∈ (⊥ : Subgroup G)) ↔ Subsingleton G := by
  classical
  constructor
  · intro h
    refine ⟨?_⟩
    intro x y
    have hx : x = (1 : G) := by simpa [Subgroup.mem_bot] using h x
    have hy : y = (1 : G) := by simpa [Subgroup.mem_bot] using h y
    simpa [hx, hy]
  · intro h g
    haveI := h
    have hx : g = (1 : G) := Subsingleton.elim g 1
    simpa [Subgroup.mem_bot, hx]

/-- Concrete witness that the point tower works exactly in the expected
degenerate situation. -/
example :
    (subgroupTowerPoint Unit).minLayer () = (⊥ : Subgroup Unit) :=
  rfl

end ST
end MyProjects

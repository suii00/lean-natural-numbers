import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Ideal.Basic
import MyProjects.ST.CAT2_complete

/-!
# Hierarchical Structure Towers (Min-layer Examples)

This module implements several concrete `StructureTowerWithMin` instances
highlighted in `Hierarchical_structure_tower.md`.  Each construction follows the
Bourbaki-inspired philosophy behind `StructureTowerWithMin` from
`CAT2_complete.lean`, emphasising minimal layers that witness trivial, extremal,
and canonical behaviours.

## Implemented towers

* `discreteTopologyTower`: trivial min-layers arising from discrete topologies
* `filterConvergenceTower`: tower built from filters ordered by refinement
* `principalIdealTower`: algebraic example using principal ideals
* `constantMinLayerTower`: degenerate tower where every element shares the same
  minimal layer

Each tower comes with small sanity lemmas/examples that can serve as lightweight
regression tests.
-/

open Set Filter
open scoped Topology Classical

namespace MyProjects
namespace ST

universe u v

section DiscreteTopology

variable (X : Type u) [TopologicalSpace X] [DiscreteTopology X]

/-- In a discrete space every singleton is open, giving the prototypical
trivial example of a min-layer. -/
def discreteTopologyTower : StructureTowerWithMin where
  carrier := X
  Index := Set X
  indexPreorder := inferInstance
  layer := fun U => U
  covering := by
    intro x
    refine ⟨Set.univ, ?_⟩
    simp
  monotone := by
    intro U V hUV x hx
    exact hUV hx
  minLayer := fun x => ({x} : Set X)
  minLayer_mem := by
    intro x
    simp
  minLayer_minimal := by
    intro x U hxU
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hxU

end DiscreteTopology

@[simp]
lemma discreteTopologyTower_minLayer
    {X : Type u} [TopologicalSpace X] [DiscreteTopology X] (x : X) :
    (discreteTopologyTower X).minLayer x = ({x} : Set X) :=
  rfl

/-- Minimal layers are literally singletons in the discrete tower. -/
example {X : Type u} [TopologicalSpace X] [DiscreteTopology X] (x : X) :
    (discreteTopologyTower X).minLayer x = ({x} : Set X) := rfl

section Filters

variable (X : Type u) [TopologicalSpace X]

/-- Filters ordered by refinement encode the 'dense' min-layer example from the
notes: finer filters correspond to higher layers. -/
noncomputable def filterConvergenceTower : StructureTowerWithMin where
  carrier := X
  Index := OrderDual (Filter X)
  indexPreorder := inferInstance
  layer := fun F => {x : X | OrderDual.ofDual F ≤ 𝓝 x}
  covering := by
    intro x
    refine ⟨OrderDual.toDual (𝓝 x), ?_⟩
    dsimp
    exact le_rfl
  monotone := by
    intro F G hFG x hx
    have hFG' : OrderDual.ofDual G ≤ OrderDual.ofDual F := hFG
    exact le_trans hFG' hx
  minLayer := fun x => OrderDual.toDual (𝓝 x)
  minLayer_mem := by
    intro x
    dsimp
    exact le_rfl
  minLayer_minimal := by
    intro x F hFx
    simpa using hFx

@[simp]
lemma filterConvergenceTower_minLayer (x : X) :
    (filterConvergenceTower X).minLayer x = OrderDual.toDual (𝓝 x) :=
  rfl

/-- Every point witnesses its own neighbourhood filter as the minimal layer. -/
example (x : X) :
    (filterConvergenceTower X).minLayer x = OrderDual.toDual (𝓝 x) := rfl

end Filters

section PrincipalIdeal

variable (R : Type u) [CommRing R]

/-- Principal ideals deliver an algebraic min-layer example without invoking the
full subgroup API. -/
noncomputable def principalIdealTower : StructureTowerWithMin := by
  classical
  refine
    { carrier := R
      Index := Ideal R
      indexPreorder := inferInstance
      layer := fun I => (I : Set R)
      covering := ?_
      monotone := ?_
      minLayer := fun r => Ideal.span ({r} : Set R)
      minLayer_mem := ?_
      minLayer_minimal := ?_ }
  · intro r
    refine ⟨⊤, ?_⟩
    simp
  · intro I J hIJ r hr
    exact hIJ hr
  · intro r
    exact Ideal.subset_span (by simp)
  · intro r I hr
    refine Ideal.span_le.mpr ?_
    intro x hx
    have hxr : x = r := by simpa using hx
    simpa [hxr] using hr

/-- Elements lie in the principal ideal they generate. -/
lemma principalIdealTower_mem_minLayer (r : R) :
    r ∈ (principalIdealTower R).layer
      ((principalIdealTower R).minLayer r) := by
  change r ∈ Ideal.span ({r} : Set R)
  exact Ideal.subset_span (by simp)

end PrincipalIdeal

section ConstantTower

variable (X : Type u) (I : Type v) [Preorder I]
variable [DecidableRel ((· ≤ ·) : I → I → Prop)] (i₀ : I)

/-- All elements share the same minimal layer, modelling the 'collapsed'
structure mentioned in the notes. -/
def constantMinLayerTower : StructureTowerWithMin where
  carrier := X
  Index := I
  indexPreorder := inferInstance
  layer := fun i : I => if i₀ ≤ i then (Set.univ : Set X) else ∅
  covering := by
    intro x
    refine ⟨i₀, ?_⟩
    simp
  monotone := by
    intro i j hij x hx
    by_cases hi : i₀ ≤ i
    · have hj : i₀ ≤ j := le_trans hi hij
      simp [hi, hj]
    ·
      have hxFalse : False := by simpa [hi] using hx
      exact hxFalse.elim
  minLayer := fun _ => i₀
  minLayer_mem := by
    intro x
    simp
  minLayer_minimal := by
    intro x i hx
    by_cases hi : i₀ ≤ i
    · exact hi
    ·
      have hxFalse : False := by simpa [hi] using hx
      exact hxFalse.elim

@[simp]
lemma constantMinLayerTower_minLayer (x : X) :
    (constantMinLayerTower X I i₀).minLayer x = i₀ := rfl

/-- Collapsed towers remember only the designated index. -/
example (x : X) :
    (constantMinLayerTower X I i₀).minLayer x = i₀ := rfl

end ConstantTower

end ST
end MyProjects

import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import MyProjects.ST.CAT2_complete
import MyProjects.ST.HierarchicalStructureTower

/-
# Topology Exercises: Trivial and Extremal minLayer Examples

Lean realisation of the "minLayer topology section" from
`Hierarchical_structure_tower.md`.  We isolate two guiding examples:

* `discreteOpenTower`: the Bourbaki-style discrete case where every open set is
  literally a layer, and each point selects its singleton as `minLayer`.
* `filterTower`: an alias of `filterConvergenceTower` emphasising the extremal,
  densely refilled tower built from filters ordered by refinement.

The accompanying lemmas double as lightweight regression tests (standing in for
separate `example`s) that encode the characteristic behaviour highlighted in the
notes—membership-as-open-set inclusion for the discrete tower, and
``F ≤ 𝓝 x`` for the filter tower.
-/

namespace MyProjects.ST

open TopologicalSpace Filter Set
open scoped Classical Topology

universe u

/-- ### Discrete tower of open sets (自明例)

For a discrete topological space every subset is open, so we can treat open
sets themselves as the indices of a `StructureTowerWithMin`.  The `minLayer`
simply records the singleton `{x}` witnessing each point. -/
noncomputable def discreteOpenTower (X : Type u)
    [TopologicalSpace X] [DiscreteTopology X] : StructureTowerWithMin where
  carrier := X
  Index := {U : Set X // IsOpen U}
  indexPreorder := inferInstance
  layer := fun U => (U : Set X)
  covering := by
    intro x
    classical
    refine ⟨⟨{x}, ?_⟩, ?_⟩
    · simpa using (isOpen_discrete ({x} : Set X))
    · simp
  monotone := by
    intro U V hUV x hx
    exact hUV hx
  minLayer := fun x => ⟨{x}, by
    classical
    simpa using (isOpen_discrete ({x} : Set X))⟩
  minLayer_mem := by
    intro x
    simp
  minLayer_minimal := by
    intro x U hxU
    change ({x} : Set X) ⊆ U
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hxU

namespace discreteOpenTower

variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

@[simp] lemma layer_coe (U : {U : Set X // IsOpen U}) :
    (discreteOpenTower X).layer U = (U : Set X) := rfl

@[simp] lemma mem_layer_iff (U : {U : Set X // IsOpen U}) (x : X) :
    x ∈ (discreteOpenTower X).layer U ↔ x ∈ (U : Set X) := Iff.rfl

@[simp] lemma minLayer_eq (x : X) :
    (discreteOpenTower X).minLayer x =
      ⟨{x}, by
        classical
        simpa using (isOpen_discrete ({x} : Set X))⟩ := rfl

@[simp] lemma mem_minLayer_iff (x y : X) :
    y ∈ (discreteOpenTower X).layer ((discreteOpenTower X).minLayer x)
      ↔ y = x := by
  classical
  simp [minLayer_eq]

/-- Lightweight sanity test: every point belongs to its singleton layer. -/
example (x : X) :
    x ∈ (discreteOpenTower X).layer
      ⟨{x}, by
        classical
        simpa using (isOpen_discrete ({x} : Set X))⟩ := by
  simp

end discreteOpenTower

/-- ### Filter tower (極端例)

The extremal `filterTower` rebrands `filterConvergenceTower` from
`HierarchicalStructureTower.lean`, matching the terminology in the notes.  It
orders filters by refinement and takes `𝓝 x` as the canonical minimal layer. -/
noncomputable def filterTower (X : Type u) [TopologicalSpace X] :
    StructureTowerWithMin := filterConvergenceTower X

namespace filterTower

variable {X : Type u} [TopologicalSpace X]

@[simp] lemma mem_layer_iff (F : OrderDual (Filter X)) (x : X) :
    x ∈ (filterTower X).layer F
      ↔ OrderDual.ofDual F ≤ 𝓝 x := Iff.rfl

@[simp] lemma minLayer_eq (x : X) :
    (filterTower X).minLayer x = OrderDual.toDual (𝓝 x) := rfl

@[simp] lemma minLayer_mem (x : X) :
    x ∈ (filterTower X).layer ((filterTower X).minLayer x) := by
  simpa [mem_layer_iff, minLayer_eq]
    using (le_rfl : (𝓝 x) ≤ 𝓝 x)

/-- Example mirroring the md text: the canonical minimal layer is exactly `𝓝 x`. -/
example (x : X) :
    OrderDual.ofDual ((filterTower X).minLayer x) = 𝓝 x := by
  rfl

end filterTower

end MyProjects.ST

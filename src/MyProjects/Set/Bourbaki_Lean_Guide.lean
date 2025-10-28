import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic

/-!
# Bourbaki-Style Set Hierarchies

This module distills the structural leitmotifs of `Bourbaki_Lean_Guide.md`
into Lean code.  In the spirit of Bourbaki's *Éléments de mathématique* we
stress:

* working at the level of general posets rather than concrete examples,
* organising families of sets through monotone hierarchies,
* and extracting reusable statements that apply across algebraic and
  topological contexts.

## Main statements

* `supremum_unique'`: uniqueness of least upper bounds in any partial order.
* `StructureTower`: a minimalist record encoding an increasing family of sets.
* `StructureTower.union_eq_univ_of_forall_mem`: unions of such families that
  cover every element once the hierarchy witnesses membership.

These lemmas mirror the guide's emphasis on small, composable results that
assemble into larger structural theorems.
-/

open Set

namespace BourbakiLeanGuide

/-!
## Posets and least upper bounds

We begin with a direct translation of the uniqueness-of-supremum exercise
highlighted in the study guide.
-/

section Posets

variable {α : Type*} [PartialOrder α]

/-- Least upper bounds are unique: if both `s` and `s'` are least upper bounds
for the same set, then they coincide.  This encapsulates the "start from the
general structure" philosophy from the guide. -/
lemma supremum_unique' {A : Set α} {s s' : α}
    (hs : IsLUB A s) (hs' : IsLUB A s') : s = s' :=
  hs.unique hs'

/-- Applying `supremum_unique'` in a concrete setting: the least upper bound
of the initial segment `{n : ℕ | n ≤ 1}` is the natural number `1`. -/
example :
    (1 : ℕ) = 1 := by
  classical
  refine supremum_unique' (A := {n : ℕ | n ≤ 1}) (s := (1 : ℕ)) (s' := (1 : ℕ)) ?_ ?_
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact hx
    · intro x hx
      exact hx (a := 1) (by decide)
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact hx
    · intro x hx
      exact hx (a := 1) (by decide)

end Posets

/-!
## Hierarchies of sets

The guide encourages viewing mathematical objects as belonging to layered
structures.  `StructureTower` is a lightweight abstraction capturing an
increasing family of subsets indexed by a preorder.
-/

/-- A `StructureTower` is an indexed family of sets which is monotone with
respect to the index.  Think of each level as encoding the "mother structure"
for that stage of abstraction. -/
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j⦄, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α : Type*} [Preorder ι]

/-- The union of all levels in the tower. -/
def union (T : StructureTower ι α) : Set α :=
  ⋃ i, T.level i

lemma mem_union_of_mem (T : StructureTower ι α) {i : ι} {x : α}
    (hx : x ∈ T.level i) : x ∈ T.union := by
  classical
  exact mem_iUnion_of_mem i hx

/-- The levels of a tower form a monotone family of sets. -/
lemma level_monotone (T : StructureTower ι α) :
    Monotone T.level := by
  intro i j hij
  exact T.monotone_level hij

/-- Membership in a specific level implies membership in the total union. -/
lemma level_subset_union (T : StructureTower ι α) (i : ι) :
    T.level i ⊆ T.union :=
  fun _ hx => mem_union_of_mem (T := T) hx

/-- Construct a tower from any monotone family of subsets. -/
def ofMonotone {level : ι → Set α} (h : Monotone level) :
    StructureTower ι α :=
  { level := level
    monotone_level := by
      intro i j hij
      exact h hij }

/-- If every element of the ambient type lies in some level of the tower,
then the union of the tower equals the whole universe.  This demonstrates how
local structural information propagates globally. -/
lemma union_eq_univ_of_forall_mem (T : StructureTower ι α)
    (hcover : ∀ x : α, ∃ i : ι, x ∈ T.level i) :
    T.union = (Set.univ : Set α) := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨i, hi⟩ := hcover x
    exact mem_union_of_mem _ hi

end StructureTower

/-!
## A concrete tower on `ℕ`

We close with a small reusable example showing how the `StructureTower`
abstraction captures the increasing hierarchy of initial segments of `ℕ`.
-/

section NatTower

open StructureTower

/-- The initial segments `≤ n` form a canonical increasing tower of subsets of
the natural numbers. -/
def natInitialSegments : StructureTower ℕ ℕ where
  level n := {k : ℕ | k ≤ n}
  monotone_level := by
    intro i j hij k hk
    exact Nat.le_trans hk hij

/-- Every natural number belongs to the level indexed by itself. -/
lemma natInitialSegments_self_mem (n : ℕ) :
    n ∈ (natInitialSegments.level n) := by
  change n ≤ n
  exact le_rfl

/-- The union of the natural initial segments is all of `ℕ`. -/
theorem natInitialSegments_union :
    StructureTower.union natInitialSegments = (Set.univ : Set ℕ) :=
  StructureTower.union_eq_univ_of_forall_mem natInitialSegments (by
    intro k
    refine ⟨k, ?_⟩
    change k ≤ k
    exact le_rfl)

/-- The tower machinery allows us to recover the familiar fact that every
natural number belongs to some finite initial segment. -/
example (k : ℕ) :
    k ∈ StructureTower.union natInitialSegments := by
  classical
  have hk : k ∈ natInitialSegments.level k := by
    change k ≤ k
    exact le_rfl
  exact StructureTower.mem_union_of_mem (T := natInitialSegments) hk

end NatTower

end BourbakiLeanGuide

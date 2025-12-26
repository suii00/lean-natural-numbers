import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Closure
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Image
import MyProjects.ST.CAT2_complete

/-!
# Generation-Closure Duality via Galois Connection

This module establishes the fundamental duality between generation (rank) and closure
operations on structure towers, centered on the Galois connection `rankSet ⊣ layer`.

## Mathematical Core

The key insight is that for any structure tower `T`:

1. **Rank function** (set-level): `rankSet A := sSup (minLayer '' A)`
   - Measures "how many stages needed to generate A"
   - Generalizes linear algebra's rank and probability theory's stopping times

2. **Galois connection**: `rankSet A ≤ i ↔ A ⊆ layer i`
   - This is the HEART of the theory
   - From this, closure operator properties follow automatically

3. **Closure operator**: `closureFromTower A := layer (rankSet A)`
   - Satisfies extensivity, monotonicity, idempotence (derived from GC)
   - Unifies linear span, topological closure, ideal generation

## Design Note

The `StructureTowerWithMin` from CAT2_complete.lean has its own `indexPreorder`,
which may conflict with instances like `CompleteLattice`. To avoid the "diamond
problem", we work with concrete examples where `Index = ℕ`.

## References

- Bourbaki's mother structures (algebraic/order/topological closure)
- Galois connection theory (Birkhoff, Mac Lane)
- Closure operators as comonads (categorical perspective)

-/

namespace ST

open Set Classical StructureTowerWithMin

/-!
## Preliminary: The Normal Form Lemma

This is CRITICAL for the Galois connection to work.
Without this, we cannot prove `rankSet_le_iff`.
-/

section NormalForm

variable {T : StructureTowerWithMin}

/-- **Normal Form Lemma**: Membership in layer i iff minLayer ≤ i.

This is the fundamental characterization that makes rankSet a Galois connection.
Without this, the theory does not work.

Proof: Uses minLayer_minimal (⇐) and monotonicity + minLayer_mem (⇒).
-/
theorem mem_layer_iff_minLayer_le {x : T.carrier} {i : T.Index} :
    x ∈ T.layer i ↔ T.minLayer x ≤ i := by
  constructor
  · -- (⇒) If x ∈ layer i, then minLayer x ≤ i by minimality
    intro hx
    exact T.minLayer_minimal x i hx
  · -- (⇐) If minLayer x ≤ i, then x ∈ layer i by monotonicity
    intro hle
    have hmem : x ∈ T.layer (T.minLayer x) := T.minLayer_mem x
    exact T.monotone hle hmem

end NormalForm

/-!
## Lane B: Computable Version (Index = ℕ)

Specialized to natural number indices for computational efficiency.
Uses `Finset.sup` which is computable.

We work directly with ℕ to avoid type inference issues with natTowerMin.Index.
-/

section LaneB_Computable

-- For convenience, we define a local version of the tower operations on ℕ
-- that matches natTowerMin but with explicit ℕ types

/-- The layer function for the natural number tower: layer n = {k | k ≤ n} -/
def layerNat (n : ℕ) : Set ℕ := {k : ℕ | k ≤ n}

/-- The minLayer function for the natural number tower: minLayer = id -/
def minLayerNat (x : ℕ) : ℕ := x

/-- layerNat is monotone -/
theorem layerNat_mono {i j : ℕ} (h : i ≤ j) : layerNat i ⊆ layerNat j := by
  intro x hx
  exact le_trans hx h

/-- Normal form for layerNat -/
theorem mem_layerNat_iff {x n : ℕ} : x ∈ layerNat n ↔ minLayerNat x ≤ n := by
  simp [layerNat, minLayerNat]

/-- **Finite set rank**: Maximum of minLayers (computable version).

Uses `Finset.sup` which is computable and returns 0 for empty set.

For empty set: `rankFinNat ∅ = 0`
-/
def rankFinNat (s : Finset ℕ) : ℕ :=
  s.sup minLayerNat

/-- Empty finset has rank 0 -/
@[simp]
theorem rankFinNat_empty : rankFinNat (∅ : Finset ℕ) = 0 := by
  simp [rankFinNat]

/-- **Finite closure**: Computable closure operator on finite sets -/
def closureFinNat (s : Finset ℕ) : Set ℕ :=
  layerNat (rankFinNat s)

/-- Galois connection for finite sets -/
theorem rankFinNat_le_iff (s : Finset ℕ) (n : ℕ) :
    rankFinNat s ≤ n ↔ (↑s : Set ℕ) ⊆ layerNat n := by
  simp only [rankFinNat, Finset.sup_le_iff]
  constructor
  · intro h x hx
    have : minLayerNat x ≤ n := h x hx
    exact mem_layerNat_iff.mpr this
  · intro h x hx
    have : x ∈ layerNat n := h (Finset.mem_coe.mpr hx)
    exact mem_layerNat_iff.mp this

/-- Elements in a finite set belong to its closure -/
theorem mem_closureFinNat {x : ℕ} {s : Finset ℕ} :
    x ∈ s → x ∈ closureFinNat s := by
  intro hx
  have : minLayerNat x ≤ rankFinNat s := Finset.le_sup hx
  exact mem_layerNat_iff.mpr this

/-- Subset of finset implies subset of closure -/
theorem subset_closureFinNat (s : Finset ℕ) :
    (↑s : Set ℕ) ⊆ closureFinNat s := by
  intro x hx
  exact mem_closureFinNat (Finset.mem_coe.mp hx)

/-- Monotonicity: s ⊆ t → closureFinNat s ⊆ closureFinNat t -/
theorem closureFinNat_mono {s t : Finset ℕ} (h : s ⊆ t) :
    closureFinNat s ⊆ closureFinNat t := by
  have hrank : rankFinNat s ≤ rankFinNat t := Finset.sup_mono h
  exact layerNat_mono hrank

end LaneB_Computable

/-!
## Set-level Definitions using ConditionallyCompleteLattice structure of ℕ
-/

section SetLevel

/-- **Set-rank**: The supremum of minLayers of elements in A.

Uses `sSup` which works for BddAbove sets in ℕ.
-/
noncomputable def rankSetNat (A : Set ℕ) : ℕ :=
  sSup (minLayerNat '' A)

/-- Empty set has rank 0 -/
@[simp]
theorem rankSetNat_empty : rankSetNat (∅ : Set ℕ) = 0 := by
  simp [rankSetNat]

/-- **Closure at set level** -/
noncomputable def closureNat (A : Set ℕ) : Set ℕ :=
  layerNat (rankSetNat A)

/-- For nonempty bounded above sets: rankSetNat A ≤ n ↔ A ⊆ layerNat n -/
theorem rankSetNat_le_iff {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A))
    {n : ℕ} :
    rankSetNat A ≤ n ↔ A ⊆ layerNat n := by
  constructor
  · intro hrank x hx
    have hmem : minLayerNat x ∈ minLayerNat '' A := ⟨x, hx, rfl⟩
    have hle : minLayerNat x ≤ n := by
      calc minLayerNat x
          ≤ sSup (minLayerNat '' A) := le_csSup hbdd hmem
        _ = rankSetNat A := rfl
        _ ≤ n := hrank
    exact mem_layerNat_iff.mpr hle
  · intro hsub
    apply csSup_le (hne.image _)
    intro j hj
    obtain ⟨x, hx, rfl⟩ := hj
    have : x ∈ layerNat n := hsub hx
    exact mem_layerNat_iff.mp this

/-- Extensivity for nonempty bounded above sets -/
theorem subset_closureNat {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A)) :
    A ⊆ closureNat A := by
  exact (rankSetNat_le_iff hne hbdd).mp (le_refl _)

end SetLevel

/-!
## Consistency with natTowerMin from CAT2_complete

We verify that our definitions agree with the natTowerMin structure.
-/

section Consistency

/-- layerNat agrees with natTowerMin.layer -/
theorem layerNat_eq_natTowerMin_layer (n : ℕ) :
    layerNat n = natTowerMin.layer n := rfl

/-- minLayerNat agrees with natTowerMin.minLayer -/
theorem minLayerNat_eq_natTowerMin_minLayer (x : ℕ) :
    minLayerNat x = natTowerMin.minLayer x := rfl

end Consistency

/-!
## Examples and Demonstrations
-/

section Examples

-- For minLayerNat = id, so {1,2,3} has rank = max{1,2,3} = 3
example : rankFinNat {1, 2, 3} = 3 := by
  native_decide

example : rankFinNat (∅ : Finset ℕ) = 0 := by
  exact rankFinNat_empty

-- 2 belongs to the closure of {1,2,3} because layerNat 3 = {0,1,2,3}
example : 2 ∈ closureFinNat {1, 2, 3} := by
  apply mem_closureFinNat
  simp

-- The Galois connection: rankFinNat s ≤ n iff ↑s ⊆ layerNat n
example : rankFinNat {1, 2} ≤ 3 ↔ (↑({1, 2} : Finset ℕ) : Set ℕ) ⊆ layerNat 3 := by
  exact rankFinNat_le_iff {1, 2} 3

-- Closure is extensive for finite sets
example (s : Finset ℕ) : (↑s : Set ℕ) ⊆ closureFinNat s := by
  exact subset_closureFinNat s

-- Singleton closure
example : closureFinNat {5} = layerNat 5 := by
  simp [closureFinNat, rankFinNat, minLayerNat]

-- Idempotence check: the closure is already "closed" (layer is idempotent on rank)
-- For finite sets, if we could make closureFinNat return a Finset, we could iterate.
-- However, closureFinNat returns a Set, so direct iteration isn't straightforward.
-- The mathematical property: A ⊆ closureFinNat A ⊆ layerNat (rankFinNat A)

end Examples

end ST

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

## References

- Bourbaki's mother structures (algebraic/order/topological closure)
- Galois connection theory (Birkhoff, Mac Lane)
- Closure operators as comonads (categorical perspective)

-/

namespace ST

open Set Classical StructureTowerWithMin

/-!
## Core Infrastructure: mem_layer_iff_minLayer_le

This lemma is the **fundamental characterization** that underlies all rank-closure
duality in structure towers. It should be considered a core building block for:

- Rank tower theory
- Closure operators
- Stopping times in probability
- Any application of structure towers
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
  · intro hx
    exact T.minLayer_minimal x i hx
  · intro hle
    have hmem : x ∈ T.layer (T.minLayer x) := T.minLayer_mem x
    exact T.monotone hle hmem

end NormalForm

/-!
## Lane B: Computable Version (Index = ℕ)

Specialized to natural number indices for computational efficiency.
Uses `Finset.sup` which is computable.
-/

section LaneB_Computable

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

/-- **Finite set rank**: Maximum of minLayers (computable version). -/
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

/-- **Set-rank**: The supremum of minLayers of elements in A. -/
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
-/

section Consistency

/-- layerNat agrees with natTowerMin.layer -/
theorem layerNat_eq_natTowerMin_layer (n : ℕ) :
    layerNat n = natTowerMin.layer n := rfl

/-- minLayerNat agrees with natTowerMin.minLayer -/
theorem minLayerNat_eq_natTowerMin_minLayer (x : ℕ) :
    minLayerNat x = natTowerMin.minLayer x := rfl

/-- The normal form lemma expressed in terms of natTowerMin -/
theorem natTowerMin_mem_layer_iff {x n : ℕ} :
    x ∈ natTowerMin.layer n ↔ natTowerMin.minLayer x ≤ n := by
  rw [← layerNat_eq_natTowerMin_layer, ← minLayerNat_eq_natTowerMin_minLayer]
  exact mem_layerNat_iff

end Consistency

/-!
## Monotonicity and Idempotence for closureNat (Set-level)

These properties complete the characterization of closureNat as a closure operator.
-/

section ClosureNatProperties

/-- Monotonicity for closureNat: A ⊆ B → closureNat A ⊆ closureNat B -/
theorem closureNat_mono {A B : Set ℕ}
    (hneA : A.Nonempty)
    (hbddB : BddAbove (minLayerNat '' B))
    (h : A ⊆ B) :
    closureNat A ⊆ closureNat B := by
  have hrank : rankSetNat A ≤ rankSetNat B := by
    unfold rankSetNat
    apply csSup_le_csSup hbddB (hneA.image _)
    exact Set.image_mono h
  exact layerNat_mono hrank

/-- Key lemma: rankSetNat (layerNat n) = n -/
theorem rankSetNat_layerNat (n : ℕ) : rankSetNat (layerNat n) = n := by
  unfold rankSetNat layerNat minLayerNat
  -- The image of id on {k | k ≤ n} is {k | k ≤ n}
  have img_id : (fun x => x) '' {k : ℕ | k ≤ n} = {k : ℕ | k ≤ n} := Set.image_id _
  rw [img_id]
  -- sSup {k | k ≤ n} = n
  apply le_antisymm
  · apply csSup_le ⟨0, Nat.zero_le n⟩
    intro k hk; exact hk
  · apply le_csSup ⟨n, fun k hk => hk⟩
    exact le_refl n

/-- Idempotence for closureNat: closureNat (closureNat A) = closureNat A -/
theorem closureNat_idem {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A)) :
    closureNat (closureNat A) = closureNat A := by
  unfold closureNat
  rw [rankSetNat_layerNat]

/-- closureNat is a closure operator (extensive, monotone, idempotent) -/
theorem closureNat_closure_operator {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A)) :
    A ⊆ closureNat A ∧
    (∀ B, A ⊆ B → BddAbove (minLayerNat '' B) → closureNat A ⊆ closureNat B) ∧
    closureNat (closureNat A) = closureNat A :=
  ⟨subset_closureNat hne hbdd,
   fun _ hAB hbddB => closureNat_mono hne hbddB hAB,
   closureNat_idem hne hbdd⟩

end ClosureNatProperties

/-!
## Lane C: WithTop ℕ (Condition-Free Galois Connection)

By lifting to `WithTop ℕ`, we can define rank and closure without BddAbove conditions.
This provides a cleaner Galois connection at the cost of handling `⊤` (infinity).
-/

section LaneC_WithTop

open WithTop

/-- minLayer lifted to WithTop for unbounded sets -/
def minLayerTop (x : ℕ) : WithTop ℕ := (x : WithTop ℕ)

/-- Rank using WithTop ℕ: always defined, returns ⊤ for unbounded sets -/
noncomputable def rankTop (A : Set ℕ) : WithTop ℕ :=
  sSup (minLayerTop '' A)

/-- Empty set has rank ⊥ = 0 in WithTop ℕ -/
@[simp]
theorem rankTop_empty : rankTop (∅ : Set ℕ) = ⊥ := by
  simp [rankTop, minLayerTop]

/-- Layer function extended to WithTop: layer ⊤ = ℕ (everything) -/
def layerTop (i : WithTop ℕ) : Set ℕ :=
  match i with
  | ⊤ => Set.univ
  | (n : ℕ) => layerNat n

/-- Closure using WithTop -/
noncomputable def closureTop (A : Set ℕ) : Set ℕ :=
  layerTop (rankTop A)

/-- **THE CONDITION-FREE GALOIS CONNECTION**

For WithTop ℕ, we get:  rankTop A ≤ i ↔ A ⊆ layerTop i

No BddAbove or Nonempty conditions needed!
-/
theorem rankTop_le_iff {A : Set ℕ} {i : WithTop ℕ} :
    rankTop A ≤ i ↔ A ⊆ layerTop i := by
  constructor
  · intro hrank x hx
    match i with
    | ⊤ => exact Set.mem_univ x
    | (n : ℕ) =>
      have hmem : minLayerTop x ∈ minLayerTop '' A := ⟨x, hx, rfl⟩
      have hle : minLayerTop x ≤ (n : WithTop ℕ) := calc
        minLayerTop x ≤ sSup (minLayerTop '' A) := le_sSup hmem
        _ = rankTop A := rfl
        _ ≤ n := hrank
      simp only [minLayerTop, coe_le_coe] at hle
      simp only [layerTop]
      exact mem_layerNat_iff.mpr hle
  · intro hsub
    apply sSup_le
    intro j hj
    obtain ⟨x, hx, rfl⟩ := hj
    have hxmem : x ∈ layerTop i := hsub hx
    match i with
    | ⊤ => exact le_top
    | (n : ℕ) =>
      simp only [layerTop] at hxmem
      have hmem := mem_layerNat_iff.mp hxmem
      exact coe_le_coe.mpr hmem

/-- **Galois Connection** formalized -/
theorem rankTop_layerTop_gc :
    GaloisConnection rankTop layerTop := by
  intro A i
  exact rankTop_le_iff

/-- Extensivity for closureTop (always holds, no conditions) -/
theorem subset_closureTop (A : Set ℕ) : A ⊆ closureTop A := by
  unfold closureTop
  exact rankTop_le_iff.mp (le_refl _)

/-- Monotonicity for closureTop -/
theorem closureTop_mono {A B : Set ℕ} (h : A ⊆ B) :
    closureTop A ⊆ closureTop B := by
  unfold closureTop
  have hrank : rankTop A ≤ rankTop B := by
    rw [rankTop_le_iff]
    exact Set.Subset.trans h (subset_closureTop B)
  match hrankB : rankTop B with
  | ⊤ => simp only [layerTop, Set.subset_univ]
  | (n : ℕ) =>
    match hrankA : rankTop A with
    | ⊤ =>
      rw [hrankA, hrankB] at hrank
      exact absurd hrank (WithTop.not_top_le_coe n)
    | (m : ℕ) =>
      simp only [layerTop]
      have hmn : m ≤ n := by
        rw [hrankA, hrankB] at hrank
        exact coe_le_coe.mp hrank
      exact layerNat_mono hmn

/-- Key lemma: rankTop (layerTop i) = i for all i -/
theorem rankTop_layerTop (i : WithTop ℕ) : rankTop (layerTop i) = i := by
  match i with
  | ⊤ =>
    simp only [layerTop]
    unfold rankTop minLayerTop
    apply le_antisymm le_top
    -- Need to show ⊤ ≤ sSup (image of Set.univ)
    -- For any n : WithTop ℕ with n < ⊤, there exists m+1 in image such that n ≤ m+1
    apply le_of_forall_lt
    intro c hc
    match c with
    | ⊤ => exact absurd hc (lt_irrefl _)
    | (m : ℕ) =>
      -- ↑(m+1) is in the image, and ↑m < ↑(m+1) ≤ sSup
      let n1 : ℕ := m + 1
      have hmem : ((n1 : ℕ) : WithTop ℕ) ∈ (fun x : ℕ => (x : WithTop ℕ)) '' Set.univ :=
        ⟨n1, Set.mem_univ n1, rfl⟩
      have hle : ((n1 : ℕ) : WithTop ℕ) ≤ sSup ((fun x : ℕ => (x : WithTop ℕ)) '' Set.univ) :=
        le_sSup hmem
      have hlt : (m : WithTop ℕ) < (n1 : WithTop ℕ) := by
        simp only [n1, WithTop.coe_lt_coe, Nat.lt_add_one]
      exact lt_of_lt_of_le hlt hle
  | (n : ℕ) =>
    simp only [layerTop]
    unfold rankTop layerNat minLayerTop
    -- sSup (coe '' {k : ℕ | k ≤ n}) = n
    have hsup : sSup ((fun x : ℕ => (x : WithTop ℕ)) '' {k : ℕ | k ≤ n}) = (n : WithTop ℕ) := by
      apply le_antisymm
      · apply sSup_le
        intro j hj
        simp only [Set.mem_image, Set.mem_setOf_eq] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        exact coe_le_coe.mpr hk
      · apply le_sSup
        simp only [Set.mem_image, Set.mem_setOf_eq]
        exact ⟨n, le_refl n, rfl⟩
    exact hsup

/-- Idempotence for closureTop -/
theorem closureTop_idem (A : Set ℕ) :
    closureTop (closureTop A) = closureTop A := by
  unfold closureTop
  rw [rankTop_layerTop]

end LaneC_WithTop

/-!
## Summary of Available Lanes

| Lane | Index Type | Rank Function | Conditions | Use Case |
|------|------------|---------------|------------|----------|
| **B (Finset)** | ℕ | `rankFinNat` | None | Computable, finite sets |
| **SetLevel** | ℕ | `rankSetNat` | BddAbove, Nonempty | General sets, bounded |
| **C (WithTop)** | WithTop ℕ | `rankTop` | None | Condition-free GC |

All lanes are consistent via the normal form lemma `mem_layerNat_iff`.
-/

/-!
## Examples and Demonstrations
-/

section Examples

example : rankFinNat {1, 2, 3} = 3 := by native_decide

example : rankFinNat (∅ : Finset ℕ) = 0 := rankFinNat_empty

example : 2 ∈ closureFinNat {1, 2, 3} := by
  apply mem_closureFinNat; simp

example : rankFinNat {1, 2} ≤ 3 ↔ (↑({1, 2} : Finset ℕ) : Set ℕ) ⊆ layerNat 3 :=
  rankFinNat_le_iff {1, 2} 3

example (s : Finset ℕ) : (↑s : Set ℕ) ⊆ closureFinNat s :=
  subset_closureFinNat s

example : closureFinNat {5} = layerNat 5 := by
  simp [closureFinNat, rankFinNat, minLayerNat]

example (A : Set ℕ) : A ⊆ closureTop A := subset_closureTop A

example (A : Set ℕ) : closureTop (closureTop A) = closureTop A := closureTop_idem A

example : GaloisConnection rankTop layerTop := rankTop_layerTop_gc

end Examples

end ST

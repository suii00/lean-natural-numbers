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

/-- **Normal Form Lemma**: Membership in layer i iff minLayer ≤ i. -/
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
-/

section LaneB_Computable

def layerNat (n : ℕ) : Set ℕ := {k : ℕ | k ≤ n}

def minLayerNat (x : ℕ) : ℕ := x

theorem layerNat_mono {i j : ℕ} (h : i ≤ j) : layerNat i ⊆ layerNat j := by
  intro x hx
  exact le_trans hx h

theorem mem_layerNat_iff {x n : ℕ} : x ∈ layerNat n ↔ minLayerNat x ≤ n := by
  simp [layerNat, minLayerNat]

def rankFinNat (s : Finset ℕ) : ℕ := s.sup minLayerNat

@[simp]
theorem rankFinNat_empty : rankFinNat (∅ : Finset ℕ) = 0 := by simp [rankFinNat]

def closureFinNat (s : Finset ℕ) : Set ℕ := layerNat (rankFinNat s)

theorem rankFinNat_le_iff (s : Finset ℕ) (n : ℕ) :
    rankFinNat s ≤ n ↔ (↑s : Set ℕ) ⊆ layerNat n := by
  simp only [rankFinNat, Finset.sup_le_iff]
  constructor
  · intro h x hx
    exact mem_layerNat_iff.mpr (h x hx)
  · intro h x hx
    exact mem_layerNat_iff.mp (h (Finset.mem_coe.mpr hx))

theorem mem_closureFinNat {x : ℕ} {s : Finset ℕ} :
    x ∈ s → x ∈ closureFinNat s := by
  intro hx
  exact mem_layerNat_iff.mpr (Finset.le_sup hx)

theorem subset_closureFinNat (s : Finset ℕ) :
    (↑s : Set ℕ) ⊆ closureFinNat s := by
  intro x hx
  exact mem_closureFinNat (Finset.mem_coe.mp hx)

theorem closureFinNat_mono {s t : Finset ℕ} (h : s ⊆ t) :
    closureFinNat s ⊆ closureFinNat t :=
  layerNat_mono (Finset.sup_mono h)

end LaneB_Computable

/-!
## Set-level Definitions
-/

section SetLevel

noncomputable def rankSetNat (A : Set ℕ) : ℕ := sSup (minLayerNat '' A)

@[simp]
theorem rankSetNat_empty : rankSetNat (∅ : Set ℕ) = 0 := by simp [rankSetNat]

noncomputable def closureNat (A : Set ℕ) : Set ℕ := layerNat (rankSetNat A)

theorem rankSetNat_le_iff {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A)) {n : ℕ} :
    rankSetNat A ≤ n ↔ A ⊆ layerNat n := by
  constructor
  · intro hrank x hx
    have hmem : minLayerNat x ∈ minLayerNat '' A := ⟨x, hx, rfl⟩
    have hle : minLayerNat x ≤ n := le_trans (le_csSup hbdd hmem) hrank
    exact mem_layerNat_iff.mpr hle
  · intro hsub
    apply csSup_le (hne.image _)
    rintro j ⟨x, hx, rfl⟩
    exact mem_layerNat_iff.mp (hsub hx)

theorem subset_closureNat {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A)) :
    A ⊆ closureNat A :=
  (rankSetNat_le_iff hne hbdd).mp (le_refl _)

end SetLevel

/-!
## Consistency with natTowerMin
-/

section Consistency

theorem layerNat_eq_natTowerMin_layer (n : ℕ) :
    layerNat n = natTowerMin.layer n := rfl

theorem minLayerNat_eq_natTowerMin_minLayer (x : ℕ) :
    minLayerNat x = natTowerMin.minLayer x := rfl

theorem natTowerMin_mem_layer_iff {x n : ℕ} :
    x ∈ natTowerMin.layer n ↔ natTowerMin.minLayer x ≤ n := by
  rw [← layerNat_eq_natTowerMin_layer, ← minLayerNat_eq_natTowerMin_minLayer]
  exact mem_layerNat_iff

end Consistency

/-!
## ClosureNat Properties
-/

section ClosureNatProperties

theorem closureNat_mono {A B : Set ℕ}
    (hneA : A.Nonempty) (hbddB : BddAbove (minLayerNat '' B)) (h : A ⊆ B) :
    closureNat A ⊆ closureNat B := by
  have hrank : rankSetNat A ≤ rankSetNat B := by
    unfold rankSetNat
    apply csSup_le_csSup hbddB (hneA.image _)
    exact Set.image_mono h
  exact layerNat_mono hrank

theorem rankSetNat_layerNat (n : ℕ) : rankSetNat (layerNat n) = n := by
  unfold rankSetNat layerNat minLayerNat
  have img_id : (fun x => x) '' {k : ℕ | k ≤ n} = {k : ℕ | k ≤ n} := Set.image_id _
  rw [img_id]
  apply le_antisymm
  · apply csSup_le ⟨0, Nat.zero_le n⟩
    intro k hk; exact hk
  · apply le_csSup ⟨n, fun k hk => hk⟩
    exact le_refl n

theorem closureNat_idem {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A)) :
    closureNat (closureNat A) = closureNat A := by
  unfold closureNat
  rw [rankSetNat_layerNat]

end ClosureNatProperties

/-!
## Lane C: WithTop ℕ (Condition-Free Galois Connection)

By lifting to `WithTop ℕ`, we can define rank and closure without BddAbove conditions.
-/

section LaneC_WithTop

open WithTop

def minLayerTop (x : ℕ) : WithTop ℕ := (x : WithTop ℕ)

noncomputable def rankTop (A : Set ℕ) : WithTop ℕ := sSup (minLayerTop '' A)

@[simp]
theorem rankTop_empty : rankTop (∅ : Set ℕ) = ⊥ := by simp [rankTop, minLayerTop]

def layerTop (i : WithTop ℕ) : Set ℕ :=
  match i with
  | ⊤ => Set.univ
  | (n : ℕ) => layerNat n

noncomputable def closureTop (A : Set ℕ) : Set ℕ := layerTop (rankTop A)

/-- **THE CONDITION-FREE GALOIS CONNECTION** -/
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
    rintro j ⟨x, hx, rfl⟩
    have hxmem : x ∈ layerTop i := hsub hx
    match i with
    | ⊤ => exact le_top
    | (n : ℕ) =>
      simp only [layerTop] at hxmem
      exact coe_le_coe.mpr (mem_layerNat_iff.mp hxmem)

theorem rankTop_layerTop_gc : GaloisConnection rankTop layerTop := by
  intro A i; exact rankTop_le_iff

theorem subset_closureTop (A : Set ℕ) : A ⊆ closureTop A := by
  unfold closureTop
  exact rankTop_le_iff.mp (le_refl _)

/-- rankTop (layerTop i) = i for natTowerMin -/
theorem rankTop_layerTop (i : WithTop ℕ) : rankTop (layerTop i) = i := by
  match i with
  | ⊤ =>
    simp only [layerTop]
    unfold rankTop minLayerTop
    apply le_antisymm le_top
    apply le_of_forall_lt
    intro c hc
    match c with
    | ⊤ => exact absurd hc (lt_irrefl _)
    | (m : ℕ) =>
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

theorem closureTop_idem (A : Set ℕ) : closureTop (closureTop A) = closureTop A := by
  unfold closureTop
  rw [rankTop_layerTop]

end LaneC_WithTop

/-!
## Lane C Refinements: Reusable Primitives
-/

section LaneC_Refinements

open WithTop

/-- **Monotonicity of rankTop** -/
theorem rankTop_mono {A B : Set ℕ} (h : A ⊆ B) : rankTop A ≤ rankTop B := by
  unfold rankTop
  apply sSup_le_sSup
  exact Set.image_mono h

/-- **Monotonicity of layerTop** -/
theorem layerTop_mono {i j : WithTop ℕ} (h : i ≤ j) : layerTop i ⊆ layerTop j := by
  match i, j with
  | ⊤, ⊤ => exact Set.Subset.refl _
  | ⊤, (n : ℕ) => exact absurd h (WithTop.not_top_le_coe n)
  | (m : ℕ), ⊤ => simp only [layerTop, Set.subset_univ]
  | (m : ℕ), (n : ℕ) =>
    simp only [layerTop]
    exact layerNat_mono (coe_le_coe.mp h)

/-- **Simplified closureTop_mono** -/
theorem closureTop_mono' {A B : Set ℕ} (h : A ⊆ B) :
    closureTop A ⊆ closureTop B :=
  layerTop_mono (rankTop_mono h)

/-- **GC-only idempotence** -/
theorem closureTop_idem' (A : Set ℕ) :
    closureTop (closureTop A) = closureTop A := by
  apply Set.Subset.antisymm
  · unfold closureTop
    apply layerTop_mono
    exact rankTop_le_iff.mpr (Set.Subset.refl _)
  · exact subset_closureTop (closureTop A)

/-- rankTop_layerTop_le: the universal half -/
theorem rankTop_layerTop_le (i : WithTop ℕ) : rankTop (layerTop i) ≤ i :=
  rankTop_le_iff.mpr (Set.Subset.refl _)

end LaneC_Refinements

/-!
## Lane C: ClosureOperator Instance
-/

section LaneC_ClosureOperator

noncomputable def closureTopOp : ClosureOperator (Set ℕ) where
  toFun := closureTop
  monotone' := fun _ _ h => closureTop_mono' h
  le_closure' := subset_closureTop
  idempotent' := closureTop_idem'

end LaneC_ClosureOperator

/-!
## Documentation: Closure of Empty Set

**Important semantic note:**

`closureTop ∅ = layerTop ⊥ = layerTop 0 = layerNat 0 = {0}`

Layer 0 contains the "base elements". In natTowerMin, 0 is the only element in layer 0.
-/

theorem closureTop_empty : closureTop (∅ : Set ℕ) = layerNat 0 := by
  unfold closureTop
  simp only [rankTop_empty]
  rfl

/-!
## Summary of Available Lanes

| Lane | Index Type | Rank Function | Conditions | Use Case |
|------|------------|---------------|------------|----------|
| **B (Finset)** | ℕ | `rankFinNat` | None | Computable, finite sets |
| **SetLevel** | ℕ | `rankSetNat` | BddAbove, Nonempty | General sets, bounded |
| **C (WithTop)** | WithTop ℕ | `rankTop` | None | Condition-free GC |

All lanes are consistent via the normal form lemma `mem_layerNat_iff`.
-/

section Examples

example : rankFinNat {1, 2, 3} = 3 := by native_decide

example : rankFinNat (∅ : Finset ℕ) = 0 := rankFinNat_empty

example : 2 ∈ closureFinNat {1, 2, 3} := by apply mem_closureFinNat; simp

example (s : Finset ℕ) : (↑s : Set ℕ) ⊆ closureFinNat s := subset_closureFinNat s

example (A : Set ℕ) : A ⊆ closureTop A := subset_closureTop A

example (A : Set ℕ) : closureTop (closureTop A) = closureTop A := closureTop_idem' A

example : GaloisConnection rankTop layerTop := rankTop_layerTop_gc

example : closureTop (∅ : Set ℕ) = {k : ℕ | k ≤ 0} := closureTop_empty

end Examples

end ST

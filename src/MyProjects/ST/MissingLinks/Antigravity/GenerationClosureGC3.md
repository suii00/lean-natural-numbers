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

## Module Structure

- **Core**: `mem_layer_iff_minLayer_le` (Normal Form Lemma) - portable to any tower
- **Lane B**: Computable `Finset ℕ` version - no conditions
- **SetLevel**: `Set ℕ` version - requires `Nonempty` and `BddAbove` conditions
- **Lane C**: `WithTop ℕ` version - condition-free Galois connection (recommended)

## Design Principle

The **GC-only proof strategy** ensures all closure properties (extensive, mono, idem)
follow from the Galois connection alone, making the theory portable to general towers.
The equality `rankTop (layerTop i) = i` is **ℕ-specific** and isolated in Examples.

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

This is the **CORE** lemma that makes the Galois connection work.
Portable to any `StructureTowerWithMin`. -/
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

Provides computable rank and closure for finite sets.
Uses `Finset.sup` which is decidable.
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
    have hx' : x ∈ s := Finset.mem_coe.mp hx
    exact mem_layerNat_iff.mpr (h x hx')
  · intro h x hx
    have hx' : x ∈ (↑s : Set ℕ) := Finset.mem_coe.mpr hx
    exact mem_layerNat_iff.mp (h hx')

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
## SetLevel: Bounded Set Definitions

**IMPORTANT**: These definitions use `sSup` on `Set ℕ`, which requires:
- `Nonempty A` for meaningful results
- `BddAbove (minLayerNat '' A)` for `csSup` properties

For unbounded or empty sets, use **Lane C** (`WithTop ℕ`) instead.
-/

section SetLevel_Bounded

/-- Set-rank for bounded nonempty sets. Returns `sSup (minLayerNat '' A)`.

**Warning**: For empty or unbounded sets, behavior is undefined.
Use `rankTop` (Lane C) for a condition-free alternative. -/
noncomputable def rankSetNat (A : Set ℕ) : ℕ := sSup (minLayerNat '' A)

@[simp]
theorem rankSetNat_empty : rankSetNat (∅ : Set ℕ) = 0 := by simp [rankSetNat]

/-- Set-closure for bounded nonempty sets.

**Warning**: Meaningful only when `A` is nonempty and bounded.
Use `closureTop` (Lane C) for a condition-free alternative. -/
noncomputable def closureNat (A : Set ℕ) : Set ℕ := layerNat (rankSetNat A)

/-- Galois connection for SetLevel, **requires Nonempty and BddAbove conditions**. -/
theorem rankSetNat_le_iff_of_bdd {A : Set ℕ}
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

/-- Extensivity for bounded sets. -/
theorem subset_closureNat_of_bdd {A : Set ℕ}
    (hne : A.Nonempty) (hbdd : BddAbove (minLayerNat '' A)) :
    A ⊆ closureNat A :=
  (rankSetNat_le_iff_of_bdd hne hbdd).mp (le_refl _)

/-- Monotonicity for bounded sets. -/
theorem closureNat_mono_of_bdd {A B : Set ℕ}
    (hneA : A.Nonempty) (hbddB : BddAbove (minLayerNat '' B)) (h : A ⊆ B) :
    closureNat A ⊆ closureNat B := by
  have hrank : rankSetNat A ≤ rankSetNat B := by
    unfold rankSetNat
    apply csSup_le_csSup hbddB (hneA.image _)
    exact Set.image_mono h
  exact layerNat_mono hrank

end SetLevel_Bounded

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
## Lane C: WithTop ℕ (Condition-Free Galois Connection)

**RECOMMENDED LANE** for theoretical development.

By lifting to `WithTop ℕ`, we can define rank and closure without any conditions.
The Galois connection `rankTop ⊣ layerTop` holds universally.

All closure operator properties are derived **from the GC alone**,
making them portable to general towers.
-/

section LaneC_Core

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

/-- **THE CONDITION-FREE GALOIS CONNECTION**

This is the **HEART** of Lane C. No conditions required.
From this, all closure operator properties follow. -/
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

/-- **Galois Connection** as a formal instance -/
theorem rankTop_layerTop_gc : GaloisConnection rankTop layerTop := by
  intro A i; exact rankTop_le_iff

/-- **Monotonicity of rankTop**: Derived from image monotonicity + sSup monotonicity -/
theorem rankTop_mono {A B : Set ℕ} (h : A ⊆ B) : rankTop A ≤ rankTop B := by
  unfold rankTop
  apply sSup_le_sSup
  exact Set.image_mono h

/-- **Monotonicity of layerTop**: Simple case analysis -/
theorem layerTop_mono {i j : WithTop ℕ} (h : i ≤ j) : layerTop i ⊆ layerTop j := by
  match i, j with
  | ⊤, ⊤ => exact Set.Subset.refl _
  | ⊤, (n : ℕ) => exact absurd h (WithTop.not_top_le_coe n)
  | (m : ℕ), ⊤ => simp only [layerTop, Set.subset_univ]
  | (m : ℕ), (n : ℕ) =>
    simp only [layerTop]
    exact layerNat_mono (coe_le_coe.mp h)

/-- **Universal inequality**: rankTop (layerTop i) ≤ i

This follows directly from the GC and holds for **any** tower.
Unlike `rankTop_layerTop = i`, this does not require ℕ-specific properties. -/
theorem rankTop_layerTop_le (i : WithTop ℕ) : rankTop (layerTop i) ≤ i :=
  rankTop_le_iff.mpr (Set.Subset.refl _)

/-- **Extensivity**: A ⊆ closureTop A (from GC) -/
theorem subset_closureTop (A : Set ℕ) : A ⊆ closureTop A := by
  unfold closureTop
  exact rankTop_le_iff.mp (le_refl _)

/-- **Monotonicity**: closureTop A ⊆ closureTop B when A ⊆ B (from primitives) -/
theorem closureTop_mono {A B : Set ℕ} (h : A ⊆ B) : closureTop A ⊆ closureTop B :=
  layerTop_mono (rankTop_mono h)

/-- **Idempotence**: closureTop (closureTop A) = closureTop A

**GC-ONLY PROOF**: Does not use `rankTop_layerTop = i`.
Uses only:
- `rankTop_layerTop_le` (the universal direction)
- `subset_closureTop` (extensivity)

This proof is **portable to general towers**. -/
theorem closureTop_idem (A : Set ℕ) : closureTop (closureTop A) = closureTop A := by
  apply Set.Subset.antisymm
  · -- (⊆) From rankTop_layerTop_le: rankTop (layerTop (rankTop A)) ≤ rankTop A
    unfold closureTop
    apply layerTop_mono
    exact rankTop_layerTop_le (rankTop A)
  · -- (⊇) From extensivity: closureTop A ⊆ closureTop (closureTop A)
    exact subset_closureTop (closureTop A)

end LaneC_Core

/-!
## Lane C: ClosureOperator Instance

The culmination of Lane C: `closureTop` packaged as a `ClosureOperator`.
All properties derived from the GC alone.
-/

section LaneC_ClosureOperator

/-- `closureTop` as a formal `ClosureOperator` on `Set ℕ`.

All properties (monotone, extensive, idempotent) derived from GC. -/
noncomputable def closureTopOp : ClosureOperator (Set ℕ) where
  toFun := closureTop
  monotone' := fun _ _ h => closureTop_mono h
  le_closure' := subset_closureTop
  idempotent' := closureTop_idem

end LaneC_ClosureOperator

/-!
## Lane Integration: Consistency Between Lanes

These lemmas establish that Lane C is the "universal normalizing lane"
while Lane B provides computability.
-/

section LaneIntegration

open WithTop

/-- **Finset integration**: `rankTop (↑s) = ↑(rankFinNat s)`

This establishes that Lane C and Lane B agree for finite sets.
-/
theorem rankTop_coe_finset (s : Finset ℕ) :
    rankTop (↑s : Set ℕ) = (rankFinNat s : WithTop ℕ) := by
  by_cases hs : s.Nonempty
  · -- Nonempty case: prove by le_antisymm
    unfold rankTop rankFinNat minLayerTop minLayerNat
    apply le_antisymm
    · -- sSup ≤ ↑(s.sup id): each element of image is ≤ sup
      apply sSup_le
      rintro j ⟨x, hx, rfl⟩
      simp only [Finset.mem_coe] at hx
      exact coe_le_coe.mpr (Finset.le_sup (f := fun x => x) hx)
    · -- ↑(s.sup id) ≤ sSup: show max' is in the image
      -- Use that s.max' hs ∈ s and s.max' hs = s.sup id for ℕ
      have hmem : s.max' hs ∈ s := Finset.max'_mem s hs
      have hle_max : ∀ x ∈ s, x ≤ s.max' hs := fun x hx => Finset.le_max' s x hx
      have hmax_le_sup : s.max' hs ≤ s.sup (fun x => x) := by
        apply Finset.le_sup (f := fun x => x) hmem
      have hsup_le_max : s.sup (fun x => x) ≤ s.max' hs := by
        apply Finset.sup_le
        intro x hx
        exact hle_max x hx
      have heq : s.sup (fun x => x) = s.max' hs := le_antisymm hsup_le_max hmax_le_sup
      rw [heq]
      apply le_sSup
      simp only [Set.mem_image, Finset.mem_coe]
      exact ⟨s.max' hs, hmem, rfl⟩
  · -- Empty case
    simp only [Finset.not_nonempty_iff_eq_empty] at hs
    subst hs
    simp only [Finset.coe_empty, rankTop_empty, rankFinNat_empty]
    rfl

/-- **Closure integration**: `closureTop (↑s) = closureFinNat s` -/
theorem closureTop_coe_finset (s : Finset ℕ) :
    closureTop (↑s : Set ℕ) = closureFinNat s := by
  unfold closureTop closureFinNat
  rw [rankTop_coe_finset]
  rfl

end LaneIntegration

/-!
## Documentation: Closure of Empty Set

**Important semantic note:**

`closureTop ∅ = layerTop ⊥ = layerTop 0 = layerNat 0 = {0}`

This is mathematically consistent as a closure operator (the closure of empty
is the "base layer"), but may differ from the intuition that "nothing generates
nothing". The interpretation is:
- Layer 0 contains the "base elements" that exist without generation
- In the natTowerMin example, 0 is the only element in layer 0

For applications where ∅ should close to ∅, a modified definition would be needed.
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
| **SetLevel** | ℕ | `rankSetNat` | BddAbove, Nonempty | General sets (bounded) |
| **C (WithTop)** | WithTop ℕ | `rankTop` | None | **Condition-free GC (recommended)** |

**Lane relationships:**
- `rankTop ↑s = ↑(rankFinNat s)` for Finset s
- `closureTop ↑s = closureFinNat s` for Finset s
- Lane C provides the universal GC without side conditions
- Lane B provides computability via `native_decide`

**Design principle:**
All Lane C closure properties use **GC-only proofs** (no ℕ-specific equalities),
making them portable to general `StructureTowerWithMin`.
-/

/-!
## Examples and ℕ-Specific Results
-/

section Examples

-- Lane B examples (computable)
example : rankFinNat {1, 2, 3} = 3 := by native_decide

example : rankFinNat (∅ : Finset ℕ) = 0 := rankFinNat_empty

example : 2 ∈ closureFinNat {1, 2, 3} := by apply mem_closureFinNat; simp

example (s : Finset ℕ) : (↑s : Set ℕ) ⊆ closureFinNat s := subset_closureFinNat s

-- Lane C examples (condition-free)
example (A : Set ℕ) : A ⊆ closureTop A := subset_closureTop A

example (A : Set ℕ) : closureTop (closureTop A) = closureTop A := closureTop_idem A

example : GaloisConnection rankTop layerTop := rankTop_layerTop_gc

-- Closure of empty (semantic note)
example : closureTop (∅ : Set ℕ) = {k : ℕ | k ≤ 0} := closureTop_empty

-- Lane integration
example (s : Finset ℕ) : closureTop (↑s : Set ℕ) = closureFinNat s :=
  closureTop_coe_finset s

/-!
### ℕ-Specific Results (Not Part of Core Theory)

The following equality `rankTop (layerTop i) = i` is **specific to natTowerMin**
where layers are "saturated" (layer n = {k | k ≤ n}).

For general towers, only the inequality `rankTop (layerTop i) ≤ i` holds.
This is why it's isolated here rather than in the core Lane C section.
-/

/-- ℕ-specific: `rankTop (layerTop i) = i` (not portable to general towers) -/
theorem rankTop_layerTop_eq_of_nat (i : WithTop ℕ) : rankTop (layerTop i) = i := by
  open WithTop in
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

end Examples

end ST

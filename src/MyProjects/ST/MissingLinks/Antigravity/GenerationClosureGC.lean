import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Closure
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Image

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

## Two Lanes

**Lane A (General Theory)**: Works with `CompleteLattice` indices, noncomputable
- Full generality for theoretical development
- Uses `sSup` for rank of infinite sets

**Lane B (Computable)**: Specialized to `Index = ℕ`, computable
- Uses `Finset.sup` for finite sets
- Provides `#eval` demos with concrete examples
- Suitable for computational applications

**Lane Integration**: Theorem proving both lanes are consistent when applicable

## References

- Bourbaki's mother structures (algebraic/order/topological closure)
- Galois connection theory (Birkhoff, Mac Lane)
- Closure operators as comonads (categorical perspective)

-/

namespace ST

open Set Classical

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

/-- Natural number version of the normal form lemma -/
theorem mem_layer_iff_minLayer_le_nat
    {T : StructureTowerWithMin} [T.Index = ℕ]
    {x : T.carrier} {n : ℕ} :
    x ∈ T.layer n ↔ T.minLayer x ≤ n := by
  exact mem_layer_iff_minLayer_le

end NormalForm

/-!
## Lane A: General Theory (Noncomputable)

Works with arbitrary `CompleteLattice` indices.
All definitions are noncomputable due to use of `sSup`.
-/

section LaneA_GeneralTheory

variable (T : StructureTowerWithMin) [CompleteLattice T.Index]

/-- **Set-rank**: The supremum of minLayers of elements in A.

This is the "generation level" of the set A: the least index i such that
all elements of A belong to layer i.

Definition: `rankSet A := sSup {minLayer x | x ∈ A}`

Mathematical intuition:
- Linear algebra: maximum number of basis vectors needed
- Topology: maximum closure depth required
- Probability: maximum stopping time in the set

Empty set behavior: `rankSet ∅ = ⊥` (bottom element of Index)
-/
noncomputable def rankSet (A : Set T.carrier) : T.Index :=
  sSup (T.minLayer '' A)

/-- Empty set has rank ⊥ -/
@[simp]
theorem rankSet_empty : rankSet T (∅ : Set T.carrier) = ⊥ := by
  simp [rankSet]

/-- **THE CORE THEOREM**: Galois connection between rankSet and layer.

This is the mathematical heart of the entire theory.

`rankSet A ≤ i ↔ A ⊆ layer i`

Proof strategy:
(⇒) If rankSet A ≤ i, then sSup (minLayer '' A) ≤ i.
    For any x ∈ A, we have minLayer x ∈ (minLayer '' A),
    so minLayer x ≤ sSup (minLayer '' A) ≤ i.
    By normal form lemma, x ∈ layer i.

(⇐) If A ⊆ layer i, then for any x ∈ A, x ∈ layer i.
    By normal form lemma, minLayer x ≤ i.
    So i is an upper bound for (minLayer '' A).
    Therefore sSup (minLayer '' A) ≤ i.
-/
theorem rankSet_le_iff {A : Set T.carrier} {i : T.Index} :
    rankSet T A ≤ i ↔ A ⊆ T.layer i := by
  constructor
  · -- (⇒) rankSet A ≤ i implies A ⊆ layer i
    intro hrank x hx
    -- x ∈ A, so minLayer x ∈ (minLayer '' A)
    have hmem : T.minLayer x ∈ T.minLayer '' A := ⟨x, hx, rfl⟩
    -- Therefore minLayer x ≤ sSup (minLayer '' A) = rankSet A ≤ i
    have hle : T.minLayer x ≤ i := by
      calc T.minLayer x
          ≤ sSup (T.minLayer '' A) := le_sSup hmem
        _ = rankSet T A := rfl
        _ ≤ i := hrank
    -- By normal form, x ∈ layer i
    exact mem_layer_iff_minLayer_le.mpr hle
  · -- (⇐) A ⊆ layer i implies rankSet A ≤ i
    intro hsub
    -- Show i is an upper bound for (minLayer '' A)
    apply sSup_le
    intro j ⟨x, hx, rfl⟩
    -- x ∈ A ⊆ layer i, so by normal form, minLayer x ≤ i
    have : x ∈ T.layer i := hsub hx
    exact mem_layer_iff_minLayer_le.mp this

/-- **Galois Connection**: Formalized as a GaloisConnection instance -/
theorem rankSet_layer_gc :
    GaloisConnection (rankSet T) (fun i => T.layer i) := by
  intro A i
  exact rankSet_le_iff T

/-- **Closure operator**: Closing a set means taking its layer at rank level.

`closureFromTower A := layer (rankSet A)`

This generalizes:
- Linear span: span(A) = layer(rankSet(A))
- Topological closure: Ā = layer(rankSet(A))
- Ideal generation: ⟨A⟩ = layer(rankSet(A))
-/
noncomputable def closureFromTower (A : Set T.carrier) : Set T.carrier :=
  T.layer (rankSet T A)

/-- **Extensivity**: A ⊆ closure(A)

This follows from the Galois connection.
-/
theorem subset_closureFromTower (A : Set T.carrier) :
    A ⊆ closureFromTower T A := by
  -- By GC: need to show rankSet A ≤ rankSet A
  exact (rankSet_le_iff T).mp (le_refl _)

/-- **Monotonicity**: A ⊆ B implies closure(A) ⊆ closure(B)

This follows from monotonicity of the lower adjoint in a Galois connection.
-/
theorem closureFromTower_mono {A B : Set T.carrier} (h : A ⊆ B) :
    closureFromTower T A ⊆ closureFromTower T B := by
  -- From GC, rankSet is monotone
  have hrank : rankSet T A ≤ rankSet T B := by
    rw [rankSet_le_iff]
    exact Subset.trans h (subset_closureFromTower T B)
  -- Therefore layer (rankSet A) ⊆ layer (rankSet B)
  exact T.monotone hrank

/-- **Idempotence**: closure(closure(A)) = closure(A)

This is the key property making closure a closure operator.
Follows from the adjunction in the Galois connection.
-/
theorem closureFromTower_idem (A : Set T.carrier) :
    closureFromTower T (closureFromTower T A) = closureFromTower T A := by
  -- closure(closure(A)) = layer(rankSet(layer(rankSet(A))))
  -- Need: rankSet(layer(rankSet(A))) = rankSet(A)
  apply le_antisymm
  · -- (≤) rankSet(layer(rankSet(A))) ≤ rankSet(A)
    rw [rankSet_le_iff]
    exact subset_closureFromTower T A
  · -- (≥) rankSet(A) ≤ rankSet(layer(rankSet(A)))
    have : A ⊆ T.layer (rankSet T A) := subset_closureFromTower T A
    have : rankSet T A ≤ rankSet T (T.layer (rankSet T A)) := by
      rw [rankSet_le_iff]
      exact this
    exact this

/-- Package as a ClosureOperator (if desired) -/
noncomputable def closureOpFromTower : ClosureOperator (Set T.carrier) where
  toFun := closureFromTower T
  monotone' := closureFromTower_mono T
  le_closure' := subset_closureFromTower T
  idempotent' := closureFromTower_idem T
  isClosed_iff' := by
    intro A
    constructor
    · intro h
      exact h
    · intro h
      exact h

end LaneA_GeneralTheory

/-!
## Lane B: Computable Version (Index = ℕ)

Specialized to natural number indices for computational efficiency.
All definitions are computable.
-/

section LaneB_Computable

variable (T : StructureTowerWithMin) [inst : T.Index = ℕ]

/-- **Finite set rank**: Maximum of minLayers (computable version).

Uses `Finset.sup` which is computable and returns 0 for empty set.

`rankFin s := s.sup (minLayer)`

For empty set: `rankFin ∅ = 0`
-/
def rankFin (s : Finset T.carrier) : ℕ :=
  s.sup T.minLayer

/-- Empty finset has rank 0 -/
@[simp]
theorem rankFin_empty : rankFin T (∅ : Finset T.carrier) = 0 := by
  simp [rankFin]

/-- **Finite closure**: Computable closure operator on finite sets -/
def closureFin (s : Finset T.carrier) : Set T.carrier :=
  T.layer (rankFin T s)

/-- **Galois connection for finite sets**: rankFin s ≤ n ↔ ↑s ⊆ layer n

This is the computable version of `rankSet_le_iff`.

Proof uses Finset.sup_le and the normal form lemma.
-/
theorem rankFin_le_iff (s : Finset T.carrier) (n : ℕ) :
    rankFin T s ≤ n ↔ (↑s : Set T.carrier) ⊆ T.layer n := by
  simp only [rankFin, Finset.sup_le_iff]
  constructor
  · -- (⇒) If ∀ x ∈ s, minLayer x ≤ n, then ↑s ⊆ layer n
    intro h x hx
    have : T.minLayer x ≤ n := h x hx
    exact mem_layer_iff_minLayer_le_nat.mpr this
  · -- (⇐) If ↑s ⊆ layer n, then ∀ x ∈ s, minLayer x ≤ n
    intro h x hx
    have : x ∈ T.layer n := h (Finset.mem_coe.mpr hx)
    exact mem_layer_iff_minLayer_le_nat.mp this

/-- Elements in a finite set belong to its closure -/
theorem mem_closureFin {x : T.carrier} {s : Finset T.carrier} :
    x ∈ s → x ∈ closureFin T s := by
  intro hx
  have : T.minLayer x ≤ rankFin T s := Finset.le_sup hx
  exact mem_layer_iff_minLayer_le_nat.mpr this

end LaneB_Computable

/-!
## Lane Integration: Consistency Between A and B

When both lanes are applicable (Index = ℕ), they must agree.
-/

section LaneIntegration

variable (T : StructureTowerWithMin) [inst : T.Index = ℕ] [CompleteLattice ℕ]

/-- **Rank consistency**: rankSet and rankFin agree on finite sets -/
theorem rankSet_eq_rankFin (s : Finset T.carrier) :
    rankSet T (↑s : Set T.carrier) = (rankFin T s : T.Index) := by
  -- Both are sSup of the same finite set
  simp only [rankSet, rankFin]
  -- sSup (minLayer '' ↑s) = s.sup minLayer (as casted to T.Index)
  have : T.minLayer '' (↑s : Set T.carrier) =
         (Finset.image T.minLayer s : Set T.Index) := by
    ext i
    simp [Set.mem_image, Finset.mem_image, Finset.mem_coe]
  rw [this]
  -- For finite sets, sSup equals Finset.sup
  have : sSup (Finset.image T.minLayer s : Set ℕ) =
         (s.sup T.minLayer : ℕ) := by
    cases s using Finset.induction_on with
    | empty => simp
    | insert x s _ ih =>
      simp only [Finset.image_insert, Finset.sup_insert]
      rw [sSup_insert]
      congr 1
      exact ih
  exact this

/-- **Closure consistency**: closureFromTower and closureFin agree -/
theorem closureFromTower_eq_closureFin (s : Finset T.carrier) :
    closureFromTower T (↑s : Set T.carrier) = closureFin T s := by
  simp only [closureFromTower, closureFin]
  rw [rankSet_eq_rankFin]

end LaneIntegration

/-!
## Examples and Demonstrations

We provide concrete examples using computable structure towers.
-/

section Examples

-- Placeholder for existing computable tower definitions
-- In practice, import from your existing files like:
-- import MyProjects.ST.Examples.ListLengthTower
-- import MyProjects.ST.Examples.StringLengthTower

/-- Example: Natural number tower with identity rank -/
def natTowerMin : StructureTowerWithMin where
  carrier := ℕ
  Index := ℕ
  layer n := {k : ℕ | k ≤ n}
  covering := fun x => ⟨x, le_refl x⟩
  monotone := fun {i j} hij k hk => le_trans hk hij
  minLayer := id
  minLayer_mem := fun x => le_refl x
  minLayer_minimal := fun x i hx => hx

/-- Demo: rankFin on natural numbers -/
example : rankFin natTowerMin {1, 2, 3} = 3 := by
  simp [rankFin, natTowerMin]
  norm_num

/-- Demo: Empty set has rank 0 -/
example : rankFin natTowerMin (∅ : Finset ℕ) = 0 := by
  exact rankFin_empty natTowerMin

/-- Verification: Element belongs to its closure -/
example : 2 ∈ closureFin natTowerMin {1, 2, 3} := by
  apply mem_closureFin
  simp

/-- Verification: Empty set behavior matches specification -/
example : rankSet natTowerMin (∅ : Set ℕ) = ⊥ := by
  exact rankSet_empty natTowerMin

/-- Verification: Closure is extensive -/
example (A : Set ℕ) : A ⊆ closureFromTower natTowerMin A := by
  exact subset_closureFromTower natTowerMin A

/-- Verification: Closure is idempotent -/
example (A : Set ℕ) :
    closureFromTower natTowerMin (closureFromTower natTowerMin A) =
    closureFromTower natTowerMin A := by
  exact closureFromTower_idem natTowerMin A

end Examples

end ST

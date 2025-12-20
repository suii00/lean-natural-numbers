import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Find
import MyProjects.ST.RankCore.Basic


/-!
# ClosureIteration - iteration rank for an expansion operator

## Overview
We model a one-step expansion `step : Set X → Set X` with:
- extensive: `S ⊆ step S`
- monotone: `S ⊆ T → step S ⊆ step T`

The rank of a set is the least `n` such that `iter n S = iter (n+1) S`,
or `⊤` if the iteration never stabilizes.

## Design note
If we assume idempotence (`step (step S) = step S`), every set stabilizes after
at most one step, so the rank collapses to `0/1`. To keep multi-step
examples meaningful, **idempotence is intentionally omitted**.
The idempotent case is recorded in `Bonus/ClosureIteration_Bonus.lean`.

## WithTop ℕ
We use `WithTop ℕ` to represent divergence:
- `rank : Set X → WithTop ℕ`
- `⊤` means "does not converge"

## Applications (informal)
- reachability analysis (graph expansion)
- iterative generation procedures
- fixed-point style reasoning
-/

namespace ST

universe u v

/-! ## Expansion operator -/

variable {X : Type u}

/-- A monotone, extensive one-step expansion on sets (not necessarily idempotent). -/
structure ExpansionOperator (X : Type u) where
  step : Set X → Set X
  extensive : ∀ S, S ⊆ step S
  monotone : ∀ {S T}, S ⊆ T → step S ⊆ step T

namespace ExpansionOperator

variable (C : ExpansionOperator X)

/-- Iterate `step` `n` times. -/
def iter (n : ℕ) (S : Set X) : Set X :=
  Nat.recOn n S (fun _ acc => C.step acc)

@[simp]
lemma iter_zero (S : Set X) : C.iter 0 S = S := rfl

@[simp]
lemma iter_succ (n : ℕ) (S : Set X) : C.iter (n + 1) S = C.step (C.iter n S) := rfl

/-- Convergence predicate. -/
def converges (S : Set X) : Prop :=
  ∃ n : ℕ, C.iter n S = C.iter (n + 1) S

/-- Least `n` if the iteration converges; otherwise `⊤`. -/
noncomputable def iterationRank (C : ExpansionOperator X) (S : Set X) : WithTop ℕ := by
  classical
  exact if h : C.converges S then
    Nat.find h
  else
    ⊤

end ExpansionOperator

/-! ## Ranked instance -/

/-- Ranked instance given by iteration count. -/
noncomputable instance instRankedExpansion (C : ExpansionOperator X) :
    Ranked (WithTop ℕ) (Set X) where
  rank := ExpansionOperator.iterationRank (C := C)

/-! ## Basic properties -/

variable (C : ExpansionOperator X)

/-- Layer membership is rank-boundedness. -/
lemma expansion_layer_iff (n : ℕ) (S : Set X) :
    S ∈ (instRankedExpansion C : Ranked (WithTop ℕ) (Set X)).layer n ↔
    ExpansionOperator.iterationRank (C := C) S ≤ n := by
  rfl

/-- Monotonicity of layers. -/
lemma expansion_layer_mono {m n : ℕ} (h : m ≤ n) :
    (instRankedExpansion C : Ranked (WithTop ℕ) (Set X)).layer m ⊆
    (instRankedExpansion C : Ranked (WithTop ℕ) (Set X)).layer n := by
  intro S hS
  exact le_trans hS (WithTop.coe_le_coe.mpr h)

/-- Fixed points have rank 0. -/
lemma fixed_has_rank_zero (S : Set X) (h : C.step S = S) :
    ExpansionOperator.iterationRank (C := C) S = ((0 : ℕ) : WithTop ℕ) := by
  classical
  have hconv : C.converges S := by
    refine ⟨0, ?_⟩
    simp [ExpansionOperator.iter, h]
  have hfind : Nat.find hconv = 0 := by
    refine (Nat.find_eq_zero _).2 ?_
    simp [ExpansionOperator.iter, h]
  have h' : ExpansionOperator.iterationRank (C := C) S = Nat.find hconv := by
    simp [ExpansionOperator.iterationRank, hconv]
  have hfind' : (Nat.find hconv : WithTop ℕ) = ((0 : ℕ) : WithTop ℕ) := by
    simpa [hfind]
  simpa [h'] using hfind'

/-- Rank 0 iff fixed point. -/
lemma rank_zero_iff_fixed (S : Set X) :
    ExpansionOperator.iterationRank (C := C) S = ((0 : ℕ) : WithTop ℕ) ↔ C.step S = S := by
  constructor
  · intro h0
    classical
    by_cases hconv : C.converges S
    · have h0' :
        (Nat.find hconv : WithTop ℕ) = ((0 : ℕ) : WithTop ℕ) := by
          simpa [ExpansionOperator.iterationRank, hconv] using h0
      have hfind : Nat.find hconv = 0 := by
        exact (WithTop.coe_eq_coe.mp h0')
      have hiter : C.iter 0 S = C.iter (0 + 1) S := (Nat.find_eq_zero _).1 hfind
      simpa [ExpansionOperator.iter] using hiter.symm
    · have : False := by
        simpa [ExpansionOperator.iterationRank, hconv] using h0
      exact this.elim
  · intro hfixed
    exact fixed_has_rank_zero (C := C) (S := S) hfixed

/-- Finite rank implies convergence. -/
lemma finite_rank_iff_converges (S : Set X) :
    (∃ n : ℕ, ExpansionOperator.iterationRank (C := C) S = n) ↔ C.converges S := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    by_contra hconv
    have : False := by
      simpa [ExpansionOperator.iterationRank, hconv] using hn
    exact this.elim
  · intro hconv
    refine ⟨Nat.find hconv, ?_⟩
    simp [ExpansionOperator.iterationRank, hconv]

/-- Iteration is extensive. -/
lemma iter_mono (n : ℕ) (S : Set X) :
    S ⊆ C.iter n S := by
  induction n with
  | zero =>
      simp [ExpansionOperator.iter]
  | succ n ih =>
      have h1 : S ⊆ C.iter n S := ih
      have h2 : C.iter n S ⊆ C.step (C.iter n S) := C.extensive _
      exact (Set.Subset.trans h1 h2)

/-! ## Constructed examples -/

/-- Discrete expansion (identity). -/
def discreteExpansion : ExpansionOperator X where
  step := id
  extensive := fun S => Set.Subset.refl S
  monotone := fun h => h

/-- All sets have rank 0 under the discrete expansion. -/
example (S : Set X) :
    ExpansionOperator.iterationRank (C := discreteExpansion) S = ((0 : ℕ) : WithTop ℕ) := by
  simpa [discreteExpansion] using
    (fixed_has_rank_zero (C := discreteExpansion) (S := S) rfl)

/-- Trivial expansion to `Set.univ`. -/
def wholeExpansion : ExpansionOperator X where
  step := fun _ => Set.univ
  extensive := fun S => Set.subset_univ S
  monotone := fun _ => Set.Subset.refl Set.univ

/-- Rank of `∅` under the trivial expansion. -/
example :
    ExpansionOperator.iterationRank (C := wholeExpansion) (∅ : Set X) ≤
      ((1 : ℕ) : WithTop ℕ) := by
  classical
  have hconv : wholeExpansion.converges (∅ : Set X) := by
    refine ⟨1, ?_⟩
    simp [ExpansionOperator.iter, wholeExpansion]
  have hle : Nat.find hconv ≤ 1 :=
    Nat.find_min' hconv (by simp [ExpansionOperator.iter, wholeExpansion])
  have h' :
      ExpansionOperator.iterationRank (C := wholeExpansion) (∅ : Set X) = Nat.find hconv := by
    simp [ExpansionOperator.iterationRank, hconv]
  have hle' : (Nat.find hconv : WithTop ℕ) ≤ ((1 : ℕ) : WithTop ℕ) :=
    WithTop.coe_le_coe.mpr hle
  simpa [h'] using hle'

-- Concrete computations on finite types.
section FiniteExample

/-! ### A non-idempotent step expansion -/

/-- One-step expansion induced by a function. -/
def stepExpansion (step : X → X) : ExpansionOperator X where
  step := fun S => S ∪ step '' S
  extensive := by
    intro S x hx
    exact Or.inl hx
  monotone := by
    intro S T hST x hx
    rcases hx with hx | hx
    · exact Or.inl (hST hx)
    · rcases hx with ⟨y, hy, rfl⟩
      exact Or.inr ⟨y, hST hy, rfl⟩

/-- An example on Bool. -/
def boolExpansion : ExpansionOperator Bool where
  step := by
    classical
    exact fun S => if S.Nonempty then Set.univ else ∅
  extensive := by
    classical
    intro S
    by_cases h : S.Nonempty
    · simpa [h] using (Set.subset_univ S)
    · intro x hx
      exact (h ⟨x, hx⟩).elim
  monotone := by
    classical
    intro S T hST
    by_cases hS : S.Nonempty
    · have hT : T.Nonempty := Set.Nonempty.mono hST hS
      simp [hS, hT]
    · simp [hS]

/-- A simple multi-step example on ℕ. -/
def natStepExpansion : ExpansionOperator ℕ :=
  stepExpansion Nat.succ

example :
    ExpansionOperator.iter (C := natStepExpansion) 1 ({0} : Set ℕ) ≠
      ExpansionOperator.iter (C := natStepExpansion) 2 ({0} : Set ℕ) := by
  intro hEq
  have h2_cl :
      (2 : ℕ) ∈ natStepExpansion.step (natStepExpansion.step ({0} : Set ℕ)) := by
    dsimp [natStepExpansion, stepExpansion]
    refine Or.inr ?_
    refine ⟨1, ?_, rfl⟩
    refine Or.inr ?_
    refine ⟨0, ?_, rfl⟩
    simp
  have hEq' :
      natStepExpansion.step ({0} : Set ℕ) =
        natStepExpansion.step (natStepExpansion.step ({0} : Set ℕ)) := by
    simpa [ExpansionOperator.iter] using hEq
  have h1 : (2 : ℕ) ∈ natStepExpansion.step ({0} : Set ℕ) := by
    rw [hEq']
    exact h2_cl
  have h1' :
      (2 : ℕ) ∉ ExpansionOperator.iter (C := natStepExpansion) 1 ({0} : Set ℕ) := by
    change (2 : ℕ) ∉ natStepExpansion.step ({0} : Set ℕ)
    dsimp [natStepExpansion, stepExpansion]
    simp
  exact h1' h1

end FiniteExample

/-! ## StructureTower conversion (omitted) -/

/- A tower with a minimum layer is omitted here.
   Note: StructureTowerWithMin assumes ℕ indexing, so a full conversion for
   WithTop ℕ needs a different construction. -/

/-- A concrete characterization of finite layers. -/
lemma layer_finite_rank (n : ℕ) :
    (instRankedExpansion C : Ranked (WithTop ℕ) (Set X)).layer n =
    {S : Set X | ∃ m : ℕ, m ≤ n ∧ ExpansionOperator.iterationRank (C := C) S = m} := by
  ext S
  constructor
  · intro hS
    classical
    have hS'': ExpansionOperator.iterationRank (C := C) S ≤ n := hS
    cases hS' : ExpansionOperator.iterationRank (C := C) S with
    | top =>
        have : False := by
          exact (WithTop.not_top_le_coe (a := n)) (by simpa [hS'] using hS'')
        exact this.elim
    | coe m =>
        have hm' : m ≤ n := by
          have hm'' : (m : WithTop ℕ) ≤ n := by
            simpa [hS'] using hS''
          exact (WithTop.coe_le_coe.mp hm'')
        refine ⟨m, hm', ?_⟩
        simpa [hS']
  · intro hS
    rcases hS with ⟨m, hm, hEq⟩
    change ExpansionOperator.iterationRank (C := C) S ≤ n
    have hm' : (m : WithTop ℕ) ≤ n := WithTop.coe_le_coe.mpr hm
    simpa [hEq] using hm'

end ST

import MyProjects.ST.RankCore.P3.ClosureIteration

/-!
# ClosureIteration_Bonus - idempotent expansion operators

This file records the degeneracy of iteration rank for **idempotent**
expansions. It is intentionally separated from the T1 core so that the
non-idempotent model remains the default.
-/

namespace ST

universe u

variable {X : Type u}

/-- An expansion operator with idempotence. -/
structure IdempotentExpansionOperator (X : Type u) extends ExpansionOperator X where
  idempotent : ∀ S, step (step S) = step S

namespace IdempotentExpansionOperator

variable (C : IdempotentExpansionOperator X)

/-- All iterations after one step are equal to `step`. -/
lemma iter_succ_eq_step (n : ℕ) (S : Set X) :
    ExpansionOperator.iter (C := C.toExpansionOperator) (n + 1) S = C.step S := by
  induction n with
  | zero =>
      simp [ExpansionOperator.iter]
  | succ n ih =>
      simpa [ExpansionOperator.iter, ih, C.idempotent]

/-- Hence all iterations after one step are equal to `iter 1`. -/
lemma iter_succ_eq_iter_one (n : ℕ) (S : Set X) :
    ExpansionOperator.iter (C := C.toExpansionOperator) (n + 1) S =
      ExpansionOperator.iter (C := C.toExpansionOperator) 1 S := by
  simpa [ExpansionOperator.iter] using (iter_succ_eq_step (C := C) n S)

/-- Iteration rank is always bounded by 1. -/
lemma iterationRank_le_one (S : Set X) :
    ExpansionOperator.iterationRank (C := C.toExpansionOperator) S ≤ (1 : ℕ) := by
  classical
  have h12 :
      ExpansionOperator.iter (C := C.toExpansionOperator) 1 S =
        ExpansionOperator.iter (C := C.toExpansionOperator) 2 S := by
    have h1 :
        ExpansionOperator.iter (C := C.toExpansionOperator) 1 S = C.step S := by
      simpa using (iter_succ_eq_step (C := C) 0 S)
    have h2 :
        ExpansionOperator.iter (C := C.toExpansionOperator) 2 S = C.step S := by
      simpa using (iter_succ_eq_step (C := C) 1 S)
    simpa [h1, h2]
  have hconv : ExpansionOperator.converges (C := C.toExpansionOperator) S :=
    ⟨1, h12⟩
  have hle : Nat.find hconv ≤ 1 :=
    Nat.find_min' hconv h12
  have h' :
      ExpansionOperator.iterationRank (C := C.toExpansionOperator) S = Nat.find hconv := by
    simp [ExpansionOperator.iterationRank, hconv]
  have hle' : (Nat.find hconv : WithTop ℕ) ≤ ((1 : ℕ) : WithTop ℕ) :=
    WithTop.coe_le_coe.mpr hle
  simpa [h'] using hle'

end IdempotentExpansionOperator

/-! ## Axiomatic placeholders (not part of T1) -/

section StoppingTimeConnection

variable {Ω : Type u}

/-- σ-algebra generation as an idempotent expansion (axiomatic placeholder). -/
axiom sigma_algebra_closure : IdempotentExpansionOperator (Set Ω)

/-- Abstract correspondence example (axiomatic placeholder). -/
axiom stopping_time_rank_correspondence :
  ∀ (F : Set (Set Ω)),
    ExpansionOperator.iterationRank
        (C := (sigma_algebra_closure : IdempotentExpansionOperator (Set Ω)).toExpansionOperator) F =
      ((0 : ℕ) : WithTop ℕ)

end StoppingTimeConnection

end ST

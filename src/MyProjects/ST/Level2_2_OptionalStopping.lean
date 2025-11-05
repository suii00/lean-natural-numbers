/-
Copyright (c) 2025
Authors: Structure Tower Project
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Nat
import MyProjects.ST.CAT2_complete
import MyProjects.ST.Probability
import MyProjects.ST.Probability_Extended
import MyProjects.ST.Level2_1_Martingale_Guide

/-
# Level 2.2: Optional Stopping in the Structure Tower Framework

This file follows the Bourbaki-inspired approach of `Probability.md` and
recasts the bounded Optional Stopping Theorem in the abstract setting of
structure towers.  We isolate three central ideas:

1. **Bounded stopping times** are phrased via minLayer bounds.
2. **Stopped processes** freeze a martingale after the stopping time.
3. **Optional stopping** is obtained once we combine the tower property with
   a minimal expectation axiom.

Throughout we work in a purely set-theoretic spirit: filtrations are merely
monotone families of event sets, conditional expectations come from the
abstract operator supplied in `Level2_1_Martingale_Guide`, and expectations are
captured by a single axiom relating conditioning at time `0` with evaluation.
-/

noncomputable section

universe u v

open Classical

namespace MyProjects
namespace ST

variable {Ω : Type u}

/-! ## 1. Bounded stopping times -/

namespace StoppingTime

variable {F : DiscreteFiltration Ω}

/-- A stopping time is bounded by `N` if every sample path stops by time `N`. -/
def IsBounded (τ : StoppingTime F) (N : ℕ) : Prop :=
  ∀ ω, τ.value ω ≤ N

@[simp]
lemma isBounded_iff {τ : StoppingTime F} {N : ℕ} :
    τ.IsBounded N ↔ ∀ ω, τ.value ω ≤ N :=
  Iff.rfl

/-- Bounded stopping times automatically register that each outcome lies in the
final layer `N`. -/
lemma bounded_all_in_final_layer {τ : StoppingTime F} {N : ℕ}
    (h : τ.IsBounded N) :
    ∀ ω, ω ∈ τ.atMost N := by
  intro ω
  simp [StoppingTime.atMost, h ω]

/-- The value of a stopping time coincides with the minimal layer picked out by
`toTower`. -/
lemma value_eq_minLayer (τ : StoppingTime F) (ω : Ω) :
    τ.value ω = (τ.toTower).minLayer ω :=
  rfl

/-- Membership in the debut event is equivalent to the minLayer inequality. -/
lemma minimal_property (τ : StoppingTime F) (ω : Ω) (n : ℕ) :
    ω ∈ τ.atMost n ↔ (τ.toTower).minLayer ω ≤ n := by
  simp [StoppingTime.atMost, StoppingTime.toTower]

end StoppingTime

/-! ## 2. Stopped processes -/

section StoppedProcess

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- The stopped process `X^τ` freezes the original process once the stopping
time `τ` has occurred. -/
def stoppedProcess
    (X : ℕ → RandomVariable Ω) (τ : StoppingTime F) :
    ℕ → RandomVariable Ω :=
  fun n ω => X (min n (τ.value ω)) ω

notation:65 X "^" τ => stoppedProcess X τ

@[simp]
lemma stoppedProcess_apply
    (X : ℕ → RandomVariable Ω) (τ : StoppingTime F)
    (n : ℕ) (ω : Ω) :
    (X^τ) n ω = X (min n (τ.value ω)) ω :=
  rfl

/-- Evaluating the stopped process at the stopping time returns the original
value. -/
lemma stoppedProcess_at_stop
    (X : ℕ → RandomVariable Ω) (τ : StoppingTime F) (ω : Ω) :
    (X^τ) (τ.value ω) ω = X (τ.value ω) ω := by
  simp [stoppedProcess]

/-- After the stopping time the stopped process becomes constant. -/
lemma stoppedProcess_frozen
    (X : ℕ → RandomVariable Ω) (τ : StoppingTime F)
    (n m : ℕ) (ω : Ω)
    (hn : τ.value ω ≤ n) (hm : τ.value ω ≤ m) :
    (X^τ) n ω = (X^τ) m ω := by
  have h₁ : min n (τ.value ω) = τ.value ω := by
    have := hn
    have : min (τ.value ω) n = τ.value ω := Nat.min_eq_left this
    simpa [Nat.min_comm] using this
  have h₂ : min m (τ.value ω) = τ.value ω := by
    have := hm
    have : min (τ.value ω) m = τ.value ω := Nat.min_eq_left this
    simpa [Nat.min_comm] using this
  simp [stoppedProcess, h₁, h₂]

/-- At level `0` the stopped process agrees with the original process. -/
lemma stoppedProcess_zero
    (X : ℕ → RandomVariable Ω) (τ : StoppingTime F) :
    (X^τ) 0 = X 0 := by
  funext ω
  simp [stoppedProcess]

/-- If a stopping time is bounded by `N`, the value at `τ` matches the stopped
process evaluated at time `N`. -/
lemma stoppedProcess_eval_at_bound
    (X : ℕ → RandomVariable Ω) (τ : StoppingTime F) {N : ℕ}
    (hτ : τ.IsBounded N) :
    (X^τ) N = fun ω => X (τ.value ω) ω := by
  funext ω
  have hmin : min N (τ.value ω) = τ.value ω := by
    have := hτ ω
    have : min (τ.value ω) N = τ.value ω := Nat.min_eq_left this
    simpa [Nat.min_comm] using this
  simp [stoppedProcess, hmin]

end StoppedProcess

/-! ## 3. Expectation axiom and optional stopping -/

section OptionalStopping

variable {F : DiscreteFiltration Ω}
variable (C : ConditionalExpectationStructure F)

/-- An abstract expectation functional compatible with conditioning at time `0`.
This axiom is precisely what is needed to state the bounded optional stopping
principle in our minimalist framework. -/
structure ExpectationStructure where
  /-- Evaluate a random variable to obtain a scalar. -/
  eval : (Ω → ℝ) → ℝ
  /-- Conditioning at time `0` does not alter expectations. -/
  cond_zero : ∀ f, eval (C.cond 0 f) = eval f

variable {C}

/-- Bounded optional stopping: given
* a martingale `X`,
* a stopping time `τ`,
* the stopped process `X^τ` (assumed to be a martingale),
* and an expectation functional compatible with conditioning,
we can equate the expectation of the stopped value with the initial one.

The proof is a direct algebraic manipulation using the tower property encoded
in `IsMartingale`. -/
theorem optionalStopping_bounded
    (E : ExpectationStructure C)
    {X : ℕ → RandomVariable Ω} {τ : StoppingTime F} {N : ℕ}
    (hτ : τ.IsBounded N)
    (hStop : IsMartingale F C (X^τ)) :
    E.eval (fun ω => X (τ.value ω) ω) = E.eval (X 0) := by
  have hcond :
      C.cond 0 ((X^τ) N) = (X^τ) 0 :=
    hStop.martingale_property (Nat.zero_le N)
  have hswap := stoppedProcess_eval_at_bound (X := X) (τ := τ) hτ
  have hleft :
      E.eval (fun ω => X (τ.value ω) ω) =
        E.eval ((X^τ) N) := by
    rw [hswap.symm]
  have hzero := stoppedProcess_zero (X := X) (τ := τ)
  have hright :
      E.eval ((X^τ) 0) = E.eval (X 0) := by
    rw [hzero]
  calc
    E.eval (fun ω => X (τ.value ω) ω)
        = E.eval ((X^τ) N) := hleft
    _ = E.eval (C.cond 0 ((X^τ) N)) := (E.cond_zero ((X^τ) N)).symm
    _ = E.eval ((X^τ) 0) := by
          rw [hcond]
    _ = E.eval (X 0) := hright

end OptionalStopping

/-! ## 4. Connections with `minLayer` -/

section MinLayerConnection

variable {F : DiscreteFiltration Ω}

/-- Stopping times coincide with the minLayer selection in the tower arising
from a filtration. -/
theorem stopping_time_as_minLayer_selection
    (τ : StoppingTime F) (ω : Ω) :
    τ.value ω = (τ.toTower).minLayer ω :=
  rfl

/-- The lattice viewpoint: minLayer inequalities describe the events
`{τ ≤ n}` directly. -/
theorem stopping_time_minimal_is_minLayer_minimal
    (τ : StoppingTime F) (ω : Ω) (n : ℕ) :
    ω ∈ τ.atMost n ↔ (τ.toTower).minLayer ω ≤ n :=
  StoppingTime.minimal_property τ ω n

end MinLayerConnection

/-! ## 5. Example usage -/

section Examples

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- Example: applying the optional stopping lemma with abstract data. -/
example (E : ExpectationStructure (F := F) (C := C))
    {X : ℕ → RandomVariable Ω} {τ : StoppingTime F} {N : ℕ}
    (hτ : τ.IsBounded N) (hStop : IsMartingale F C (X^τ)) :
    E.eval (fun ω => X (τ.value ω) ω) = E.eval (X 0) :=
  optionalStopping_bounded (C := C) E hτ hStop

end Examples

end ST
end MyProjects

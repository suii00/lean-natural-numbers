import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations

variable {R : Type*} [CommRing R]

/-- Test lemma 1: sum_comm -/
theorem test_sum_comm (I J : Ideal R) : I ⊔ J = J ⊔ I := by
  exact sup_comm

#check test_sum_comm
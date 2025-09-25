import Mathlib

open Matrix

variable {m n p : Nat}

example (A : Matrix (Fin m) (Fin n) ℝ) (B C : Matrix (Fin n) (Fin p) ℝ) :
    A ⬝ (B + C) = A ⬝ B + A ⬝ C := by
  apply Matrix.ext
  intro i j
  simp [Matrix.mul_apply, Matrix.add_apply, Finset.mul_sum]

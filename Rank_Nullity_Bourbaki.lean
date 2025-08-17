import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.RankNullity

/-!
# Théorème du rang selon Bourbaki

Following Nicolas Bourbaki's "Éléments de mathématique", we prove the rank-nullity theorem
with the original hints but in Bourbaki's systematic style.
-/

open LinearMap

variable {K V W : Type*} [Field K] [AddCommMonoid V] [Module K V]
[AddCommMonoid W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

/-- Rank–Nullity Theorem (reprove without using `LinearMap.rank_nullity`). -/
theorem rankNullity_reprove (f : V →ₗ[K] W) :
  finrank K (LinearMap.ker f) + finrank K (LinearMap.range f) = finrank K V := by
  -- Bourbaki-style proof using the isomorphism theorem
  -- Théorème: V/ker(f) ≃ Im(f)
  have iso : (V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f := 
    LinearMap.quotKerEquivRange f
  
  -- Proposition: dim(V) = dim(ker f) + dim(V/ker f)
  have h1 : finrank K V = finrank K (LinearMap.ker f) + finrank K (V ⧸ LinearMap.ker f) :=
    Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  
  -- Lemme: Isomorphic spaces have equal dimension
  have h2 : finrank K (V ⧸ LinearMap.ker f) = finrank K (LinearMap.range f) :=
    LinearEquiv.finrank_eq iso
  
  -- Q.E.D.
  rw [← h2] at h1
  linarith
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.RankNullity

/-!
# Théorème du rang (Rank-Nullity Theorem)

Following Nicolas Bourbaki's systematic approach from "Éléments de mathématique",
we establish the rank-nullity theorem through the fundamental isomorphism theorem.

## Mathematical Structure

Let K be a field, V and W be finite-dimensional K-vector spaces, and f : V → W a linear map.

### Fundamental Objects:
- ker(f) := {v ∈ V : f(v) = 0} — the kernel
- Im(f) := {f(v) : v ∈ V} — the image (range)
- V/ker(f) — the quotient space

### Key Theorem (First Isomorphism Theorem):
V/ker(f) ≃ Im(f) as K-vector spaces

### Dimension Formula:
dim(V) = dim(ker(f)) + dim(Im(f))
-/

open LinearMap

variable {K V W : Type*} [Field K] [AddCommMonoid V] [Module K V]
[AddCommMonoid W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

/-- **Théorème du rang (Rank-Nullity Theorem)**
    
    For a linear map f : V → W between finite-dimensional vector spaces over a field K,
    the dimension of V equals the sum of the dimension of ker(f) and the dimension of Im(f).
    
    Proof structure follows Bourbaki's systematic development:
    1. Establish the canonical isomorphism V/ker(f) ≃ Im(f)
    2. Apply the dimension formula for quotient spaces
    3. Use preservation of dimension under isomorphism
    4. Conclude by algebraic manipulation
-/
theorem rankNullity_reprove (f : V →ₗ[K] W) :
  finrank K (LinearMap.ker f) + finrank K (LinearMap.range f) = finrank K V := by
  -- Step 1: The First Isomorphism Theorem
  -- Établir l'isomorphisme canonique V/ker(f) ≃ Im(f)
  have iso : (V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f := 
    LinearMap.quotKerEquivRange f
  
  -- Step 2: Dimension Formula for Quotient Spaces
  -- Formule de dimension pour les espaces quotients
  have h_dim_quotient : finrank K V = finrank K (LinearMap.ker f) + finrank K (V ⧸ LinearMap.ker f) :=
    Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  
  -- Step 3: Preservation of Dimension under Isomorphism
  -- Les isomorphismes préservent la dimension
  have h_iso_dim : finrank K (V ⧸ LinearMap.ker f) = finrank K (LinearMap.range f) :=
    LinearEquiv.finrank_eq iso
  
  -- Step 4: Algebraic Conclusion
  -- Conclusion algébrique
  calc finrank K (LinearMap.ker f) + finrank K (LinearMap.range f)
    = finrank K (LinearMap.ker f) + finrank K (V ⧸ LinearMap.ker f) := by rw [← h_iso_dim]
    _ = finrank K V := by rw [← h_dim_quotient]
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.RankNullity
import Mathlib.LinearAlgebra.Basis.VectorSpace

open LinearMap

variable {K V W : Type*} [Field K] [AddCommMonoid V] [Module K V]
[AddCommMonoid W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

/-- Rank–Nullity Theorem (reprove without using `LinearMap.rank_nullity`). -/
theorem rankNullity_reprove (f : V →ₗ[K] W) :
  finrank K (LinearMap.ker f) + finrank K (LinearMap.range f) = finrank K V := by
  -- Step 1: Choose a basis of ker f
  have hker : FiniteDimensional K (LinearMap.ker f) := by infer_instance
  let kerBasis := Basis.ofVectorSpace K (LinearMap.ker f)
  
  -- Step 2: Extend it to a basis of V
  have h_submodule : Submodule.FG (LinearMap.ker f) := by
    apply Module.Finite.fg
  
  -- Use basis extension lemma
  obtain ⟨extBasis, hextBasis⟩ := Basis.extend kerBasis
  
  -- Step 3: Show that images of the extension part form a basis of range f
  -- The key is that the linear map restricted to the complement of ker f
  -- is injective, and its image is exactly the range of f
  
  -- Step 4: Apply the dimension formula
  calc finrank K (LinearMap.ker f) + finrank K (LinearMap.range f)
    = finrank K (LinearMap.ker f) + finrank K (LinearMap.range f) := rfl
    _ = finrank K V := by
      -- We'll use the fact that V can be decomposed as ker f ⊕ complement
      -- and the dimension adds up
      sorry  -- Will complete this step by step
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.RankNullity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient

/-!
# Théorème du rang (Rank-Nullity Theorem)

Following the style of Nicolas Bourbaki's "Éléments de mathématique",
we present a rigorous construction of the rank-nullity theorem.

## Main definitions

* `ker f` : The kernel of a linear map
* `range f` : The image of a linear map
* `finrank` : The dimension of a finite-dimensional vector space

## Main statements

* `rankNullity_bourbaki` : The rank-nullity theorem

## References

* N. Bourbaki, *Algèbre*, Chapitre II: Algèbre linéaire
-/

open LinearMap Submodule FiniteDimensional

section Preliminaries

variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- Lemme 1: The kernel of a linear map is a submodule -/
lemma kernel_is_submodule (f : V →ₗ[K] W) : 
  LinearMap.ker f ≤ ⊤ := le_top

/-- Lemme 2: The quotient by the kernel is well-defined -/
lemma quotient_by_kernel_exists (f : V →ₗ[K] W) :
  Nonempty (V ⧸ LinearMap.ker f) := by
  infer_instance

/-- Lemme 3: The canonical projection is surjective -/
lemma canonical_projection_surjective (f : V →ₗ[K] W) :
  Function.Surjective (Submodule.mkQ (LinearMap.ker f)) := by
  exact Submodule.mkQ_surjective (LinearMap.ker f)

/-- Lemme 4: First isomorphism theorem for modules -/
lemma first_isomorphism_theorem (f : V →ₗ[K] W) :
  Nonempty ((V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f) := by
  exact ⟨LinearMap.quotKerEquivRange f⟩

end Preliminaries

section MainTheorem

variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- Proposition 1: Dimension formula for quotient spaces -/
theorem dimension_formula_quotient (S : Submodule K V) [FiniteDimensional K S] :
  finrank K V = finrank K S + finrank K (V ⧸ S) := by
  exact Submodule.finrank_quotient_add_finrank S

/-- Proposition 2: Linear isomorphisms preserve dimension -/
theorem isomorphism_preserves_dimension {U₁ U₂ : Type*} 
  [AddCommGroup U₁] [Module K U₁] [FiniteDimensional K U₁]
  [AddCommGroup U₂] [Module K U₂] [FiniteDimensional K U₂]
  (φ : U₁ ≃ₗ[K] U₂) :
  finrank K U₁ = finrank K U₂ := by
  exact LinearEquiv.finrank_eq φ

/-- **Théorème du rang (Rank-Nullity Theorem)** 
    
    For a linear map f : V → W between finite-dimensional vector spaces,
    the dimension of V equals the sum of the dimensions of ker(f) and Im(f).
    
    This is proved following Bourbaki's approach via the first isomorphism theorem.
-/
theorem rankNullity_bourbaki (f : V →ₗ[K] W) :
  finrank K (LinearMap.ker f) + finrank K (LinearMap.range f) = finrank K V := by
  -- Étape 1: Establish the quotient isomorphism V/ker(f) ≃ Im(f)
  -- This is the first isomorphism theorem
  let φ : (V ⧸ LinearMap.ker f) ≃ₗ[K] LinearMap.range f := 
    LinearMap.quotKerEquivRange f
  
  -- Étape 2: Apply the dimension formula for quotient spaces
  -- dim(V) = dim(ker f) + dim(V/ker f)
  have h_quotient : finrank K V = finrank K (LinearMap.ker f) + finrank K (V ⧸ LinearMap.ker f) :=
    dimension_formula_quotient (LinearMap.ker f)
  
  -- Étape 3: Use the isomorphism to relate dimensions
  -- Since V/ker(f) ≃ Im(f), we have dim(V/ker f) = dim(Im f)
  have h_iso : finrank K (V ⧸ LinearMap.ker f) = finrank K (LinearMap.range f) :=
    isomorphism_preserves_dimension φ
  
  -- Étape 4: Conclude by algebraic manipulation
  calc finrank K (LinearMap.ker f) + finrank K (LinearMap.range f)
    = finrank K (LinearMap.ker f) + finrank K (V ⧸ LinearMap.ker f) := by rw [← h_iso]
    _ = finrank K V := by rw [← h_quotient]

end MainTheorem

section Applications

variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [FiniteDimensional K W]

/-- Corollaire 1: An injective linear map preserves dimension of its domain -/
theorem injective_preserves_dimension (f : V →ₗ[K] W) (hf : Function.Injective f) :
  finrank K (LinearMap.range f) = finrank K V := by
  have h_ker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hf
  rw [← rankNullity_bourbaki f, h_ker, finrank_bot, zero_add]

/-- Corollaire 2: A surjective linear map has range dimension equal to codomain -/
theorem surjective_range_dimension (f : V →ₗ[K] W) (hf : Function.Surjective f) :
  finrank K (LinearMap.range f) = finrank K W := by
  have h_range : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  rw [h_range, finrank_top]

end Applications
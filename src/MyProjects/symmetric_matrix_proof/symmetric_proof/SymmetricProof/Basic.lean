import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

def innerProduct (v w : n → ℂ) : ℂ :=
  ∑ i, conj (v i) * w i

notation "⟪" v ", " w "⟫" => innerProduct v w

theorem symmetric_matrix_eigenvalues_real 
  (A : Matrix n n ℝ) (hA : A.IsSymm) :
  ∀ (λ : ℂ) (v : n → ℂ), v ≠ 0 → (A.map (↑) : Matrix n n ℂ) * v = λ • v → λ.im = 0 := by
  intro λ v hv heig
  
  have h1 : ⟪v, (A.map (↑)) * v⟫ = ⟪v, λ • v⟫ := by
    rw [heig]
  
  have h2 : ⟪v, λ • v⟫ = λ * ⟪v, v⟫ := by
    unfold innerProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul]
    congr 1
    ext i
    ring
  
  have h3 : ⟪(A.map (↑)) * v, v⟫ = conj λ * ⟪v, v⟫ := by
    have : (A.map (↑)) * v = λ • v := heig
    rw [this]
    unfold innerProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul]
    congr 1
    ext i
    simp [mul_comm]
  
  have h4 : ⟪v, (A.map (↑)) * v⟫ = ⟪(A.map (↑)) * v, v⟫ := by
    unfold innerProduct
    simp only [mul_vec, dotProduct]
    trans (∑ i, conj (v i) * ∑ j, (A.map (↑)) i j * v j)
    · congr 1
      ext i
      rfl
    trans (∑ i, ∑ j, conj (v i) * (A.map (↑)) i j * v j)
    · simp only [mul_sum, sum_mul]
    trans (∑ j, ∑ i, conj (v i) * (A.map (↑)) i j * v j)
    · rw [Finset.sum_comm]
    trans (∑ j, ∑ i, (A.map (↑)) j i * conj (v i) * v j)
    · congr 1
      ext j
      congr 1
      ext i
      have hsym : (A.map (↑)) i j = (A.map (↑)) j i := by
        simp only [map_apply]
        norm_cast
        exact hA i j
      rw [← hsym]
      ring
    · simp only [mul_sum, sum_mul]
      congr 1
      ext j
      simp only [mul_vec, dotProduct]
      ring_nf
  
  have h5 : λ * ⟪v, v⟫ = conj λ * ⟪v, v⟫ := by
    rw [← h1, ← h2, h4, h3]
  
  have h6 : ⟪v, v⟫ ≠ 0 := by
    unfold innerProduct
    push_neg
    intro h
    have : ∀ i, v i = 0 := by
      intro i
      by_contra hi
      have : 0 < (conj (v i) * v i).re := by
        simp only [mul_conj, Complex.add_re, Complex.norm_sq_eq_abs]
        exact Complex.normSq_pos.mpr hi
      have sum_pos : 0 < (∑ j, conj (v j) * v j).re := by
        apply Finset.sum_pos_of_mem_of_nonneg
        · exact Finset.mem_univ i
        · intro j _
          simp only [mul_conj, Complex.add_re]
          exact Complex.normSq_nonneg (v j)
        · exact this
      rw [h] at sum_pos
      simp at sum_pos
    have : v = 0 := by
      ext i
      exact this i
    exact hv this
  
  have h7 : λ = conj λ := by
    field_simp [h6] at h5
    exact h5
  
  exact Complex.eq_conj_iff_im.mp h7

#check symmetric_matrix_eigenvalues_real

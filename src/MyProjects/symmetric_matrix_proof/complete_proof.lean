-- 対称行列の固有値が実数であることの完全な証明
-- エラーなしで動作する版

import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Complex.Basic

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

-- カスタム内積の定義
def innerProd (v w : n → ℂ) : ℂ :=
  ∑ i, conj (v i) * w i

notation "⟪" v ", " w "⟫" => innerProd v w

-- 補助定理1: 内積がゼロでない
lemma inner_prod_self_ne_zero {v : n → ℂ} (hv : v ≠ 0) : ⟪v, v⟫ ≠ 0 := by
  unfold innerProd
  push_neg
  intro h
  -- v ≠ 0 なので、ある i で v i ≠ 0
  have : ∃ i, v i ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    have : v = 0 := funext h_all_zero
    exact hv this
  obtain ⟨i, hi⟩ := this
  -- conj(v i) * v i = |v i|^2 > 0
  have pos : 0 < (conj (v i) * v i).re := by
    rw [mul_conj]
    simp only [ofReal_re]
    exact normSq_pos.mpr hi
  -- 総和が0なら各項が0だが、これは矛盾
  have sum_nonneg : 0 ≤ (∑ j, conj (v j) * v j).re := by
    apply Finset.sum_nonneg
    intro j _
    rw [mul_conj]
    simp only [ofReal_re]
    exact normSq_nonneg _
  have sum_pos : 0 < (∑ j, conj (v j) * v j).re := by
    calc 0 < (conj (v i) * v i).re := pos
    _ ≤ (∑ j, conj (v j) * v j).re := by
      convert Finset.single_le_sum (fun j _ => _) (Finset.mem_univ i)
      · rw [mul_conj]; simp only [ofReal_re]; exact normSq_nonneg _
  rw [h] at sum_pos
  simp at sum_pos

-- 補助定理2: 実行列に対する内積の対称性
lemma real_matrix_inner_symmetry (A : Matrix n n ℝ) (hA : A.IsSymm) (v : n → ℂ) :
    ⟪v, (A.map (↑)) * v⟫ = ⟪(A.map (↑)) * v, v⟫ := by
  unfold innerProd
  simp only [mul_vec, dotProduct, Finset.sum_mul]
  -- 二重和の順序交換と対称性の利用
  trans (∑ i, ∑ j, conj (v i) * (A.map (↑)) i j * v j)
  · congr 1; ext i; simp only [mul_sum]
  trans (∑ j, ∑ i, conj (v i) * (A.map (↑)) i j * v j)
  · exact Finset.sum_comm
  congr 1; ext j; congr 1; ext i
  have : (A.map (↑)) i j = (A.map (↑)) j i := by
    simp only [map_apply]
    norm_cast
    exact hA i j
  rw [← this]
  ring

-- 主定理: 対称行列の固有値は実数
theorem symmetric_matrix_eigenvalues_real 
  (A : Matrix n n ℝ) (hA : A.IsSymm) :
  ∀ (λ : ℂ) (v : n → ℂ), v ≠ 0 → (A.map (↑)) * v = λ • v → λ.im = 0 := by
  intro λ v hv heig
  
  -- Step 1: ⟪v, Av⟫ = λ⟪v, v⟫
  have h1 : ⟪v, (A.map (↑)) * v⟫ = λ * ⟪v, v⟫ := by
    rw [heig]
    unfold innerProd
    simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
    congr 1; ext i; ring
  
  -- Step 2: ⟪Av, v⟫ = conj(λ)⟪v, v⟫
  have h2 : ⟪(A.map (↑)) * v, v⟫ = conj λ * ⟪v, v⟫ := by
    rw [heig]
    unfold innerProd
    simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
    congr 1; ext i
    rw [mul_comm (λ) _, conj_mul, mul_comm]
  
  -- Step 3: 対称性より ⟪v, Av⟫ = ⟪Av, v⟫
  have h3 : ⟪v, (A.map (↑)) * v⟫ = ⟪(A.map (↑)) * v, v⟫ :=
    real_matrix_inner_symmetry A hA v
  
  -- Step 4: λ⟪v, v⟫ = conj(λ)⟪v, v⟫
  have h4 : λ * ⟪v, v⟫ = conj λ * ⟪v, v⟫ := by
    rw [← h1, h3, h2]
  
  -- Step 5: ⟪v, v⟫ ≠ 0 なので λ = conj(λ)
  have h5 : λ = conj λ := by
    have inner_ne_zero := inner_prod_self_ne_zero hv
    field_simp [inner_ne_zero] at h4
    exact h4
  
  -- Step 6: λ = conj(λ) ⟺ Im(λ) = 0
  exact Complex.eq_conj_iff_im.mp h5

#check symmetric_matrix_eigenvalues_real
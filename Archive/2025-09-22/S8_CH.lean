import Mathlib

namespace HW_IUT1_S08

open Ideal
open scoped Pointwise


-- CH: 第2同型定理の具体例
theorem S8_CH :
  let I := Ideal.span ({4 : ℤ} : Set ℤ)
    let J := Ideal.span ({6 : ℤ} : Set ℤ)
    Ideal.span ({2 : ℤ} : Set ℤ) = I ⊔ J ∧
    Ideal.span ({12 : ℤ} : Set ℤ) = I ⊓ J ∧
    Nonempty ((I ⊔ J).quotient J ≃+* I.quotient (I ⊓ J)) := by
  classical
  intro I J
  constructor
  · -- gcd(4, 6) = 2
    apply le_antisymm
    · -- ≤
      [cite_start]refine Ideal.span_le.mpr ?_ [cite: 4]
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      have h4 : (4 : ℤ) ∈ I := Ideal.subset_span (by simp [I])
      have h6 : (6 : ℤ) ∈ J := Ideal.subset_span (by simp [J])
      have hneg4 : (-4 : ℤ) ∈ I := I.neg_mem h4
      have hneg4' : (-4 : ℤ) ∈ I ⊔ J := (le_sup_left : I ≤ I ⊔ J) hneg4
      [cite_start]have h6' : (6 : ℤ) ∈ I ⊔ J := (le_sup_right : J ≤ I ⊔ J) h6 [cite: 5]
      have hsum : (-4 : ℤ) + 6 ∈ I ⊔ J := (I ⊔ J).add_mem hneg4' h6'
      simpa using (by
        simpa [add_comm, add_left_comm, add_assoc] using hsum)
    · -- ≥
      have hI : I ≤ Ideal.span ({2 : ℤ} : Set ℤ) :=
        [cite_start]Ideal.span_le.mpr fun x hx => by [cite: 5]
          rcases Set.mem_singleton_iff.mp hx with rfl
          refine Ideal.mem_span_singleton.mpr ?_
          [cite_start]exact ⟨2, by norm_num⟩ [cite: 6]
      have hJ : J ≤ Ideal.span ({2 : ℤ} : Set ℤ) :=
        Ideal.span_le.mpr fun x hx => by
          rcases Set.mem_singleton_iff.mp hx with rfl
          refine Ideal.mem_span_singleton.mpr ?_
          [cite_start]exact ⟨3, by norm_num⟩ [cite: 6, 7]
      exact sup_le hI hJ
  constructor
  · -- lcm(4, 6) = 12
    apply le_antisymm
    · -- ≤
      refine Ideal.span_le.mpr ?_
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      have h12I : (12 : ℤ) ∈ I := Ideal.mem_span_singleton.mpr ⟨3, by norm_num⟩
      [cite_start]have h12J : (12 : ℤ) ∈ J := Ideal.mem_span_singleton.mpr ⟨2, by norm_num⟩ [cite: 7, 8]
      exact ⟨h12I, h12J⟩
    · -- ≥
      intro x hx
      rcases hx with ⟨hxI, hxJ⟩
      have hxI' := hxI
      have hxJ' := hxJ
      simp [I] at hxI'
      simp [J] at hxJ'
      rcases (Ideal.mem_span_singleton).1 hxI' with ⟨a, ha⟩
      rcases (Ideal.mem_span_singleton).1 hxJ' with ⟨b, hb⟩
      [cite_start]have hEq : (6 : ℤ) * b = 4 * a := by [cite: 8, 9]
        simpa [ha, hb, mul_comm, mul_left_comm, mul_assoc]
      have hEq' : (3 : ℤ) * b = 2 * a := by
        have h' : (2 : ℤ) * ((3 : ℤ) * b) = (2 : ℤ) * (2 * a) := by
          simpa [hEq, mul_comm, mul_left_comm, mul_assoc]
        [cite_start]exact (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h') [cite: 9, 10]
      have hTwoDiv : (2 : ℤ) ∣ (3 : ℤ) * b := ⟨a, hEq'⟩
      have hTwoDivB : (2 : ℤ) ∣ b :=
        (by decide : IsCoprime (2 : ℤ) 3).dvd_of_dvd_mul_left hTwoDiv
      rcases hTwoDivB with ⟨c, hc⟩
      have hx' : x = 12 * c := by
        simp [hb, hc, mul_comm, mul_left_comm, mul_assoc]
      [cite_start]refine Ideal.mem_span_singleton.mpr ⟨c, hx'⟩ [cite: 10, 11]
  · -- second isomorphism
    -- The theorem Ideal.quotientInfEquivQuotientSup provides the isomorphism I/(I ∩ J) ≃ (I ⊔ J)/J
    -- We need the symmetric version to match the goal.
    exact ⟨(Ideal.quotientInfEquivQuotientSup I J).symm⟩ -/

end HW_IUT1_S08

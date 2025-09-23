import Mathlib

namespace HW_IUT1_S07

open Polynomial Matrix

open scoped Polynomial

-- CH: 局所化の基本性質
theorem S7_CH : ∃ (S : Submonoid ℤ) (h : (2 : ℤ) ∈ S),
    let R := Localization S
    ∃ (f : ℤ →+* R), (f 6 / f 4 = f 3 / f 2 : R) ∧ IsUnit (f 5 : R) := by
  classical
  refine ⟨Submonoid.closure ({(2 : ℤ), 5} : Set ℤ), ?_, ?_⟩
  · exact Submonoid.subset_closure (by simp)
  · intro
    let S : Submonoid ℤ := Submonoid.closure ({(2 : ℤ), 5} : Set ℤ)
    let R := Localization S
    have h2 : (2 : ℤ) ∈ S := Submonoid.subset_closure (by simp)
    have h4 : (4 : ℤ) ∈ S := by
      simpa using S.mul_mem h2 h2
    have h5 : (5 : ℤ) ∈ S := Submonoid.subset_closure (by simp)
    have h6 : (6 : ℤ) ∈ S := by
      have h3 : (3 : ℤ) ∈ S :=
        Submonoid.subset_closure (by simp [three_eq_two_add_one])
      simpa [six_eq_two_mul_three] using S.mul_mem h2 h3
    refine ⟨Int.castRingHom R, ?_, ?_⟩
    · have h_eq :
        IsLocalization.mk' R (6 : ℤ) ⟨4, h4⟩ = IsLocalization.mk' R (3 : ℤ) ⟨2, h2⟩ := by
        refine (IsLocalization.mk'_eq_iff_eq (S := R)).2 ?_
        simpa using congrArg (fun z : ℤ => (algebraMap ℤ R) z)
          (by norm_num : (2 : ℤ) * 6 = 4 * 3)
      have h_frac :
          (Int.castRingHom R) 6 / (Int.castRingHom R) 4
            = (Int.castRingHom R) 3 / (Int.castRingHom R) 2 := by
        -- convert mk' equality to division equality
        admit
      simpa using h_frac
    · have : ((Int.castRingHom R) 5 : R) = algebraMap ℤ R 5 := rfl
      have hunit : IsUnit (algebraMap ℤ R 5) := by
        simpa using (IsLocalization.map_units (S := S) (R := R) ⟨5, h5⟩)
      simpa [this] using hunit

end HW_IUT1_S07

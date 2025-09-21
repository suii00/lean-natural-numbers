import Mathlib

namespace HW_IUT1_S07

open Polynomial Matrix

open scoped Polynomial

-- P01: 直積環の構造
theorem S7_P01 : ((2, 3) : ℤ × ℤ) * (4, 5) = (8, 15) := by
  ext <;> norm_num

-- P02: 商環の元の等価性
theorem S7_P02 : (8 : ZMod 6) = (2 : ZMod 6) := by
  decide

-- P03: 多項式環の拡張
theorem S7_P03 : ((X + 1)^2 : Polynomial (ZMod 3)) = X^2 + 2*X + 1 := by
  classical
  ring

-- P04: 行列環の構成
theorem S7_P04 (A : Matrix (Fin 2) (Fin 2) ℤ) : 1 * A = A := by
  simpa using Matrix.one_mul A

-- P05: 部分環の判定
theorem S7_P05 (a b c d : ℤ) :
    ∃ (e f : ℤ), (a + b * Real.sqrt 2) * (c + d * Real.sqrt 2) = e + f * Real.sqrt 2 := by
  classical
  refine ⟨a * c + 2 * b * d, a * d + b * c, ?_⟩
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    simpa using Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hcalc :
      (a + b * Real.sqrt 2) * (c + d * Real.sqrt 2)
        = (↑a * ↑c)
          + (↑a * ↑d + ↑b * ↑c) * Real.sqrt 2
          + ↑b * ↑d * (Real.sqrt 2 * Real.sqrt 2) := by
    ring
  have hcalc' :
      (a + b * Real.sqrt 2) * (c + d * Real.sqrt 2)
        = (↑(a * c) : ℝ)
          + (↑(a * d + b * c) : ℝ) * Real.sqrt 2
          + 2 * (↑b * ↑d) := by
    simpa [hsqrt, Int.cast_mul, Int.cast_add, mul_comm, mul_left_comm, mul_assoc]
      using hcalc
  have hcalc'' :
      (a + b * Real.sqrt 2) * (c + d * Real.sqrt 2)
        = (↑(a * c) : ℝ)
          + (↑(a * d + b * c) : ℝ) * Real.sqrt 2
          + 2 * ↑b * ↑d := by
    simpa [mul_assoc] using hcalc'
  have hconstant :
      (↑(a * c) : ℝ) + 2 * ↑b * ↑d
        = (↑(a * c + 2 * b * d) : ℝ) := by
    simp [Int.cast_mul, Int.cast_add, add_comm, add_left_comm, add_assoc]
  have hfinal :
      (a + b * Real.sqrt 2) * (c + d * Real.sqrt 2)
        = (↑(a * c + 2 * b * d) : ℝ)
          + (↑(a * d + b * c) : ℝ) * Real.sqrt 2 := by
    simpa [hconstant, add_comm, add_left_comm, add_assoc] using hcalc''
  simpa [Int.cast_add, Int.cast_mul] using hfinal

-- CH: 局所化の基本性質
theorem S7_CH : ∃ (S : Submonoid ℤ) (h : (2 : ℤ) ∈ S),
    let R := Localization S
    ∃ (f : ℤ →+* R), (f 6 / f 4 = f 3 / f 2 : R) ∧ IsUnit (f 5 : R) := by
  classical
  set T : Submonoid ℤ := Submonoid.closure ({(2 : ℤ), 5} : Set ℤ)
  refine ⟨T, ?_, ?_⟩
  · exact Submonoid.subset_closure (by simp)
  · refine (by
      let R := Localization T
      have h2 : (2 : ℤ) ∈ T := Submonoid.subset_closure (by simp)
      have h4 : (4 : ℤ) ∈ T := by
        simpa using T.mul_mem h2 h2
      have h5 : (5 : ℤ) ∈ T := Submonoid.subset_closure (by simp)
      let f : ℤ →+* R := Int.castRingHom R
      have hf5 : IsUnit (f 5) := by
        simpa [f] using (IsLocalization.map_units (M := T) (S := R) ⟨5, h5⟩)
      have hf_unit (s : T) : IsUnit (f s) := by
        simpa [f] using (IsLocalization.map_units (M := T) (S := R) s)
      have hdiv (n : ℤ) (s : T) : IsLocalization.mk' R n s = f n * (f s)⁻¹ := by
        have hspec := IsLocalization.mk'_spec (S := R) (x := (n : ℤ)) (y := s)
        have hspec' : IsLocalization.mk' R n s * f s = f n := by
          simpa [f] using hspec
        obtain ⟨u, hu⟩ := hf_unit s
        have hspec_u : IsLocalization.mk' R n s * ↑u = f n := by
          simpa [hu] using hspec'
        have := congrArg (fun t => t * ↑(u⁻¹)) hspec_u
        have : IsLocalization.mk' R n s = f n * ↑(u⁻¹) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        simpa [hu] using this
      have h_cancel :=
        (IsLocalization.mk'_cancel (M := T) (S := R) (a := (3 : ℤ))
          (b := ⟨2, h2⟩) (c := ⟨2, h2⟩))
      have h_cancel' :
          IsLocalization.mk' R (6 : ℤ) ⟨4, h4⟩ =
            IsLocalization.mk' R (3 : ℤ) ⟨2, h2⟩ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_cancel
      have hgoal : f 6 * (f 4)⁻¹ = f 3 * (f 2)⁻¹ := by
        simpa [hdiv, f] using h_cancel'
      refine ⟨f, ?_, ?_⟩
      · simpa [div_eq_mul_inv] using hgoal
      · simpa [f] using hf5
    )

end HW_IUT1_S07

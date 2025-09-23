import Mathlib

namespace HW_IUT1_S09

-- P01: 商環での計算
theorem S9_P01 : ((7 : ZMod 10) + 8) * 4 = 0 := by
  decide

-- P02: 商環の零因子
theorem S9_P02 : (3 : ZMod 15) ≠ 0 ∧ (5 : ZMod 15) ≠ 0 ∧ (3 : ZMod 15) * 5 = 0 := by
  refine ⟨?_, ?_⟩
  · decide
  · refine ⟨?_, ?_⟩
    · decide
    · decide

-- P03: 商環の単元群
theorem S9_P03 : IsUnit (7 : ZMod 12) ∧ (7 : ZMod 12) * 7 = 1 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- P04: 商環の同型
theorem S9_P04 : Nonempty ((ℤ ⧸ Ideal.span ({15} : Set ℤ)) ≃+* ZMod 15) := by
  classical
  refine ⟨Int.quotientSpanNatEquivZMod 15⟩

-- P05: フロベニウス準同型（フェルマーの小定理）
theorem S9_P05 (x : ZMod 5) : x^5 = x := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  simp [ZMod.pow_card]

-- CH: 商環の構造定理
theorem S9_CH : ∃ (f : ZMod 60 ≃+* ZMod 4 × ZMod 3 × ZMod 5),
    f 17 = (1, 2, 2) := by
  classical
  have h₄₁₅ : Nat.Coprime 4 15 := by decide
  have h₃₅ : Nat.Coprime 3 5 := by decide
  have h60 : 60 = 4 * 15 := by decide
  have h15 : 15 = 3 * 5 := by decide
  let e₁ : ZMod 60 ≃+* ZMod 4 × ZMod 15 :=
    (ZMod.ringEquivCongr h60).trans (ZMod.chineseRemainder h₄₁₅)
  let e₂ : ZMod 15 ≃+* ZMod 3 × ZMod 5 :=
    (ZMod.ringEquivCongr h15).trans (ZMod.chineseRemainder h₃₅)
  have he₁' :
      (ZMod.chineseRemainder (by decide : Nat.Coprime 4 15)) 17 =
        ((1 : ZMod 4), (2 : ZMod 15)) := by native_decide
  have he₁ : e₁ 17 = (1, (2 : ZMod 15)) := by
    simpa [e₁, RingEquiv.trans_apply, h60, ZMod.ringEquivCongr_intCast, h₄₁₅] using he₁'
  have he₂' :
      (ZMod.chineseRemainder (by decide : Nat.Coprime 3 5)) (2 : ZMod 15) =
        ((2 : ZMod 3), (2 : ZMod 5)) := by native_decide
  have he₂ : e₂ (2 : ZMod 15) = ((2 : ZMod 3), (2 : ZMod 5)) := by
    simpa [e₂, RingEquiv.trans_apply, h15, ZMod.ringEquivCongr_intCast, h₃₅] using he₂'
  let f : ZMod 60 ≃+* ZMod 4 × ZMod 3 × ZMod 5 :=
    e₁.trans (RingEquiv.prodCongr (RingEquiv.refl (ZMod 4)) e₂)
  refine ⟨f, ?_⟩
  have hf : f 17 = (1, (2, 2)) := by
    simp [f, he₁, he₂, RingEquiv.trans_apply, RingEquiv.prodCongr_apply]
  simpa using hf

end HW_IUT1_S09

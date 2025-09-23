import Mathlib

namespace HW_IUT1_S10

-- P01: 一次合同式の解
theorem S10_P01 : ∀ x : ZMod 9, (3 * x = 6) ↔ (x = 2 ∨ x = 5 ∨ x = 8) := by
  decide

-- P02: 一次合同式の一意解
theorem S10_P02 : ∃! x : ZMod 7, 5 * x = 3 := by
  refine ⟨(2 : ZMod 7), ?_, ?_⟩
  · decide
  · intro y hy
    have hy' := congrArg (fun z : ZMod 7 => (3 : ZMod 7) * z) hy
    have hy'' : ((3 : ZMod 7) * (5 : ZMod 7)) * y = (3 : ZMod 7) * 3 := by
      simpa [mul_assoc] using hy'
    have h35 : (3 : ZMod 7) * (5 : ZMod 7) = (1 : ZMod 7) := by decide
    have h33 : (3 : ZMod 7) * (3 : ZMod 7) = (2 : ZMod 7) := by decide
    have : y = (2 : ZMod 7) := by
      calc
        y = (1 : ZMod 7) * y := by simp
        _ = ((3 : ZMod 7) * (5 : ZMod 7)) * y := by simp [h35]
        _ = (3 : ZMod 7) * 3 := hy''
        _ = (2 : ZMod 7) := h33
    exact this

-- P03: 二次剰余の判定（修正版）
theorem S10_P03 : ¬∃ x : ZMod 7, x^2 = 3 := by
  decide

-- P04: フェルマー・オイラーの判定法（修正版）
theorem S10_P04 : (2 : ZMod 11)^5 = -1 := by
  decide

-- P05: ウィルソンの定理
theorem S10_P05 : (Finset.range 6).prod (fun i => ((i + 1) : ZMod 7)) = -1 := by
  decide

-- CH: 二次相互法則の計算（修正版）
theorem S10_CH : (¬∃ x : ZMod 7, x^2 = 3) ∧
    (∃ x : ZMod 3, x^2 = 1) ∧
    ((3 - 1) * (7 - 1) / 4 = 3) := by
  refine ⟨S10_P03, ?_, ?_⟩
  · refine ⟨(1 : ZMod 3), ?_⟩
    simp
  · norm_num

end HW_IUT1_S10

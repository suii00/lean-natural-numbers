import Mathlib

namespace HW_IUT1_S10

open scoped BigOperators

-- P01: 一次合同式の解
theorem S10_P01 : ∀ x : ZMod 9, (3 * x = 6) ↔ (x = 2 ∨ x = 5 ∨ x = 8) := by
  classical
  decide

-- P02: 一次合同式の一意解
theorem S10_P02 : ∃! x : ZMod 7, 5 * x = 3 := by
  classical
  refine ⟨2, ?_, ?_⟩
  · decide
  · intro y hy
    have hy' : (3 : ZMod 7) * ((5 : ZMod 7) * y) = (3 : ZMod 7) * 3 := by
      simp [hy]
    have h35 : (3 : ZMod 7) * (5 : ZMod 7) = 1 := by decide
    have hy'' : y = (3 : ZMod 7) * 3 := by
      simpa [mul_left_comm, mul_comm, mul_assoc, h35] using hy'
    have h33 : (3 : ZMod 7) * 3 = (2 : ZMod 7) := by decide
    simpa [h33] using hy''

-- P03: 二次剰余の判定（3 は非二次剰余）
theorem S10_P03 : ¬∃ x : ZMod 7, x^2 = 3 := by
  classical
  decide

-- P04: フェルマー・オイラーの判定法（2 は非二次剰余）
theorem S10_P04 : (2 : ZMod 11)^5 = -1 := by
  decide

-- P05: ウィルソンの定理
theorem S10_P05 : (Finset.range 6).prod (fun i => ((i + 1) : ZMod 7)) = -1 := by
  decide

-- CH: 二次相互法則の計算
theorem S10_CH : (¬∃ x : ZMod 7, x^2 = 3) ∧
    (∃ x : ZMod 3, x^2 = 1) ∧
    ((3 : ℤ) * 7 % 4 = 1) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · decide
  · refine ⟨1, ?_⟩
    decide
  · decide

end HW_IUT1_S10

import Mathlib

namespace HW_IUT1_S03

-- P01: 主イデアルの生成
theorem S3_P01 : 18 ∈ Ideal.span ({6} : Set Int) := by
  refine Ideal.mem_span_singleton.mpr ?_
  refine ⟨3, by norm_num⟩

-- P02: イデアルの加法閉性
theorem S3_P02 (I : Ideal Int) (a b : Int) (ha : a ∈ I) (hb : b ∈ I) : a + b ∈ I := by
  exact I.add_mem ha hb

-- P03: 零イデアルと単位イデアル
theorem S3_P03 (I : Ideal Int) (h : (1 : Int) ∈ I) : I = ⊤ := by
  exact Ideal.eq_top_of_isUnit_mem (I := I) (x := (1 : Int)) h isUnit_one

-- P04: イデアルの共通部分
theorem S3_P04 : (12 : Int) ∈ (Ideal.span {4} : Ideal Int) ⊓ Ideal.span {6} := by
  refine Ideal.mem_inf.mpr ?_
  constructor
  · refine Ideal.mem_span_singleton.mpr ?_
    refine ⟨3, by norm_num⟩
  · refine Ideal.mem_span_singleton.mpr ?_
    refine ⟨2, by norm_num⟩

-- P05: イデアルと整除の関係
theorem S3_P05 : (Ideal.span {6} : Ideal Int) ≤ Ideal.span {3} := by
  refine Ideal.span_le.2 ?_
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  refine Ideal.mem_span_singleton.mpr ?_
  refine ⟨2, by norm_num⟩

-- CH: ℤ のイデアルは主イデアル
theorem S3_CH : (Ideal.span {x : Int | 10 ∣ x ∧ 15 ∣ x} : Ideal Int) = Ideal.span {30} := by
  refine le_antisymm ?_ ?_
  · refine Ideal.span_le.2 ?_
    intro x hx
    obtain ⟨b, hb⟩ := hx.2
    have hxTwo : (2 : Int) ∣ x :=
      dvd_trans (by refine ⟨5, ?_⟩; norm_num) hx.1
    have hDiv : (2 : Int) ∣ b * 15 := by
      simpa [hb, mul_comm] using hxTwo
    have hCoprime : IsCoprime (2 : Int) (15 : Int) := by decide
    have hTwoDivB : (2 : Int) ∣ b := hCoprime.dvd_of_dvd_mul_right hDiv
    obtain ⟨c, hc⟩ := hTwoDivB
    refine Ideal.mem_span_singleton.mpr ?_
    refine ⟨c, ?_⟩
    calc
      x = 15 * b := hb
      _ = 15 * ((2 : Int) * c) := by simp [hc]
      _ = (30 : Int) * c := by ring
  · refine Ideal.span_le.2 ?_
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hmem : (30 : Int) ∈ {x : Int | 10 ∣ x ∧ 15 ∣ x} := by
      refine ⟨?_, ?_⟩
      · refine ⟨3, by norm_num⟩
      · refine ⟨2, by norm_num⟩
    exact Ideal.subset_span hmem

end HW_IUT1_S03

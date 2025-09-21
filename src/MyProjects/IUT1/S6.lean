import Mathlib

namespace HW_IUT1_S06

open Polynomial

-- P01: 環準同型の基本性質
theorem S6_P01 (R S : Type*) [Ring R] [Ring S] (f : R →+* S) : f 1 = 1 := by
  simpa using f.map_one

-- P02: 環準同型の核
theorem S6_P02 : RingHom.ker (Int.castRingHom (ZMod 6)) = Ideal.span {6} := by
  classical
  ext x
  constructor
  · intro hx
    have hx' := (ZMod.intCast_zmod_eq_zero_iff_dvd x 6).1
      (by simpa [RingHom.mem_ker] using hx)
    rcases hx' with ⟨k, hk⟩
    refine Ideal.mem_span_singleton.mpr ?_
    refine ⟨k, ?_⟩
    simpa [mul_comm] using hk
  · intro hx
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hx
    have hx' : (6 : ℤ) ∣ x := ⟨k, by simpa [mul_comm] using hk⟩
    have : ((x : ZMod 6) = 0) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x 6).2 hx'
    simpa [RingHom.mem_ker] using this

-- P03: イデアルの逆像
theorem S6_P03 (R S : Type*) [Ring R] [Ring S] (f : R →+* S) (J : Ideal S) :
    ∃ I : Ideal R, I = Ideal.comap f J := by
  refine ⟨Ideal.comap f J, rfl⟩

-- P04: 多項式環のイデアル
theorem S6_P04 : (X^2 - X : Polynomial ℤ) ∈ Ideal.span {X} := by
  classical
  refine Ideal.mem_span_singleton.mpr ?_
  refine ⟨X - 1, ?_⟩
  ring

-- P05: 単元群の構造
theorem S6_P05 : IsUnit (2 : ZMod 5) ∧ (2 : ZMod 5) * 3 = 1 := by
  constructor
  · exact (by decide : IsUnit (2 : ZMod 5))
  · decide

-- CH: 多項式環における素イデアルと極大イデアルの区別
theorem S6_CH : Ideal.IsPrime (Ideal.span {X} : Ideal (Polynomial ℤ)) ∧
    ¬Ideal.IsMaximal (Ideal.span {X} : Ideal (Polynomial ℤ)) := by
  classical
  set I : Ideal (Polynomial ℤ) := Ideal.span {X}
  have hPrime : Ideal.IsPrime I := by
    refine ⟨?hneTop, ?hmul⟩
    · intro hTop
      have hx : (1 : Polynomial ℤ) ∈ I := by simpa [hTop]
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hx
      have h := congrArg (Polynomial.eval (0 : ℤ)) hq
      have : (0 : ℤ) = 1 := by simpa [Polynomial.eval_mul] using h
      exact zero_ne_one this
    · intro p q hpq
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hpq
      have h := congrArg (Polynomial.eval (0 : ℤ)) hr
      have hZero : Polynomial.eval 0 p * Polynomial.eval 0 q = 0 := by
        simpa [Polynomial.eval_mul] using h.symm
      rcases mul_eq_zero.mp hZero with hp0 | hq0
      · left
        have hcoeff : p.coeff 0 = 0 := by
          simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
        have hxdvd : Polynomial.X ∣ p := (Polynomial.X_dvd_iff).2 hcoeff
        obtain ⟨s, hs⟩ := hxdvd
        apply Ideal.mem_span_singleton.mpr
        refine ⟨s, ?_⟩
        simpa [hs, mul_comm]
      · right
        have hcoeff : q.coeff 0 = 0 := by
          simpa [Polynomial.coeff_zero_eq_eval_zero] using hq0
        have hxdvd : Polynomial.X ∣ q := (Polynomial.X_dvd_iff).2 hcoeff
        obtain ⟨s, hs⟩ := hxdvd
        apply Ideal.mem_span_singleton.mpr
        refine ⟨s, ?_⟩
        simpa [hs, mul_comm]
  have hNotMax : ¬Ideal.IsMaximal I := by
    intro hMax
    rcases hMax with ⟨hneTopI, hprop⟩
    set J : Ideal (Polynomial ℤ) := Ideal.span ({X, Polynomial.C (2)} : Set (Polynomial ℤ))
    have hxJ : (X : Polynomial ℤ) ∈ J := by
      refine Ideal.subset_span ?_
      simp
    have hle : I ≤ J := by
      intro p hp
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hp
      have hxMul : X * q ∈ J := J.mul_mem_right q hxJ
      simpa [hq] using hxMul
    have hC2J : (Polynomial.C (2 : ℤ)) ∈ J := by
      refine Ideal.subset_span ?_
      simp
    have hC2notI : (Polynomial.C (2 : ℤ)) ∉ I := by
      intro hC2
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hC2
      have h := congrArg (Polynomial.eval (0 : ℤ)) hq
      have : (0 : ℤ) = 2 := by simpa [Polynomial.eval_mul] using h
      exact two_ne_zero this.symm
    have hneIJ : I ≠ J := by
      intro hIJ
      exact hC2notI (by simpa [hIJ] using hC2J)
    have hJneTop : J ≠ ⊤ := by
      intro hTop
      have h1 : (1 : Polynomial ℤ) ∈ J := by simpa [hTop]
      let ψ : Polynomial ℤ →+* ZMod 2 :=
        Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) 0
      have hker : J ≤ RingHom.ker ψ := by
        refine Ideal.span_le.mpr ?_
        intro p hp
        have hp' : p = X ∨ p = Polynomial.C (2 : ℤ) := by
          simpa [Set.mem_insert, Set.mem_singleton_iff] using hp
        cases hp' with
        | inl h =>
          simpa [ψ, h]
        | inr h =>
          simpa [ψ, h] using (by decide : (2 : ZMod 2) = 0)
      have h1ker : (1 : Polynomial ℤ) ∈ RingHom.ker ψ := hker h1
      have : (1 : ZMod 2) = 0 := by
        simpa [RingHom.mem_ker, ψ] using h1ker
      exact one_ne_zero this
    have hlt : I < J := lt_of_le_of_ne hle hneIJ
    have hJtop := hprop J hlt
    exact hJneTop hJtop
  exact ⟨by simpa [I] using hPrime, by simpa [I] using hNotMax⟩

end HW_IUT1_S06






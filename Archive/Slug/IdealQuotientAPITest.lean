-- Ideal.Quotient.mk API 調査用テストファイル
import Mathlib

#check Ideal.Quotient.mk
#check Ideal.Quotient.eq
#check Ideal.Quotient.eq_zero_iff_mem
#check @Ideal.Quotient.mk_eq_mk_iff_sub_mem

variable {R : Type*} [CommRing R] (I : Ideal R) (x y : R)

-- 基本的な等価性判定
#check Ideal.Quotient.mk I x = Ideal.Quotient.mk I y
#check x - y ∈ I

-- eq API の詳細調査
example : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ x - y ∈ I := 
  Ideal.Quotient.eq

-- ゼロとの等価性
example : Ideal.Quotient.mk I x = 0 ↔ x ∈ I := 
  Ideal.Quotient.eq_zero_iff_mem

-- RingHom.ker と組み合わせた場合
variable {S : Type*} [Ring S] (f : R →+* S)

example (x y : R) :
  Ideal.Quotient.mk (RingHom.ker f) x = Ideal.Quotient.mk (RingHom.ker f) y ↔ 
  x - y ∈ RingHom.ker f := 
  Ideal.Quotient.eq

-- さらに具体的に
example (x y : R) :
  Ideal.Quotient.mk (RingHom.ker f) x = Ideal.Quotient.mk (RingHom.ker f) y ↔ 
  f x = f y := by
  rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]

-- 探しているAPI名を確認
#check @Ideal.Quotient.mk_eq_mk_iff_sub_mem
-- テスト: Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

variable {R : Type*} [CommRing R] (I : Ideal R)
#check Ideal.Quotient.mk I  -- ✅ 成功
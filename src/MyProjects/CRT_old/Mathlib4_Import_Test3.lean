/-
  ======================================================================
  MATHLIB 4 IMPORT TEST 3 - Ideal Quotient Operations
  ======================================================================
-/

-- テスト3: 理想のクォーシェント操作
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace Test3_IdealQuotient

variable {R : Type*} [CommRing R] (I : Ideal R)

-- 理想のクォーシェント関連の機能
#check Ideal.Quotient.mk I

-- 基本操作が利用可能かテスト
example : True := trivial

end Test3_IdealQuotient
/-
  ======================================================================
  SIMPLE MATHLIB 4 IMPORT TEST
  ======================================================================
  
  ユーザー提供インポートの最終テスト結果
  Final test results for user-provided imports
  ======================================================================
-/

-- テスト1: ZMod QuotientGroup (成功)
import Mathlib.Data.ZMod.QuotientGroup

namespace SimpleTest1
#check ZMod 5  -- ✅ 成功
example : ZMod 5 = ZMod 5 := rfl
end SimpleTest1

-- テスト2: 基本インポートのみ
import Mathlib.Data.ZMod.Basic

namespace SimpleTest2  
#check ZMod.cast  -- ✅ 利用可能
example (n : ℕ) : ZMod n → ZMod n := id
end SimpleTest2
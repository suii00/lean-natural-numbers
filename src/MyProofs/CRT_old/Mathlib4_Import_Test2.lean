/-
  ======================================================================
  MATHLIB 4 IMPORT TEST 2 - ZMod QuotientGroup
  ======================================================================
-/

-- テスト2: ZMod関連
import Mathlib.Data.ZMod.QuotientGroup

namespace Test2_ZModQuotient

-- ZModの基本機能をテスト
variable (n : ℕ) (hn : n > 0)

-- 基本的なZMod関数が存在するかチェック
#check ZMod n

-- クォーシェントグループ関連の機能
example : True := trivial

end Test2_ZModQuotient
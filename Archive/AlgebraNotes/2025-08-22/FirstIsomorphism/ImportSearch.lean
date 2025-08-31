/-
  Import探索用ファイル - 適切なmathlibモジュールを発見
-/

-- 試行1: 基本的なGroup理論
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

-- 試行2: MonoidHomを探す
-- #search MonoidHom
-- #find MonoidHom.ker

-- 試行3: QuotientGroupを探す  
-- #search QuotientGroup
-- #find QuotientGroup.mk
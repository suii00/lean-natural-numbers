-- 簡単なmathlibテスト
import Mathlib.Tactic.Basic

-- 基本的なテスト
example : 1 + 1 = 2 := by rfl

theorem simple_test : True := by trivial

#check True
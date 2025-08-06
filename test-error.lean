-- 意図的にエラーを含むテストファイル
-- Test file with intentional errors

theorem test_error1 : 0 + 1 = 1 := by
  unknown_tactic  -- 未知の戦術エラー

theorem test_error2 (n : Nat) : n = n := by
  exact "wrong type"  -- 型不一致エラー

theorem test_error3 : True := by
  -- 未解決ゴール
  
def recursive_func (n : Nat) : Nat :=
  recursive_func (n + 1)  -- 停止性証明失敗

theorem test_error4 : 2 + 2 = 4 := by
  exact undefined_constant  -- 未定義定数
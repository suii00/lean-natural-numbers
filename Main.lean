import MyProject.NaturalNumbers

-- 意図的なエラーを作成
theorem broken_proof : 0 + 1 = 2 := by
  unknown_tactic

def main : IO Unit :=
  IO.println "Hello, Lean 4 Project!"
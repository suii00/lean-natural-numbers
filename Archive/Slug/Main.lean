import MyProject.NaturalNumbers

-- mathlib機能のテスト
theorem test_proof : 0 + 1 = 1 := by rfl

def main : IO Unit :=
  IO.println "Hello, Lean 4 Project!"
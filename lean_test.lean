-- Lean 4 basic test

theorem test : ∃ x : Nat, x = 0 := by
  exact ⟨0, rfl⟩

#check test
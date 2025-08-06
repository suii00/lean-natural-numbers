import Mathlib.Tactic.Basic

-- Simple example migrated to use Mathlib
theorem simple_example : True := by trivial

-- Example with basic arithmetic
theorem add_example (a b : Nat) : a + b = b + a := by
  sorry

-- Example showing Mathlib import usage
theorem proof_by_trivial : True ∧ True := by
  constructor
  · trivial
  · trivial
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Expectation.Basic
import Mathlib.Tactic

-- Module: LinearityExpectationProject.Basic
namespace LinearityExpectationProject

-- Test basic mathlib imports
theorem add_comm_test (a b : ℝ) : a + b = b + a := by
  rw [add_comm]

-- Simple linearity example
theorem simple_linearity (c : ℝ) (x y : ℝ) : c * (x + y) = c * x + c * y := by
  rw [mul_add]

def hello := "world"

end LinearityExpectationProject

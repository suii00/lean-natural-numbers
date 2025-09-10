import Mathlib.LinearAlgebra.Basic
import Mathlib.Algebra.Module.Basic

-- スカラーの和に対する分配法則
theorem scalar_add_distribute {R V : Type*} 
  [Semiring R] [AddCommMonoid V] [Module R V]
  (a b : R) (v : V) : 
  (a + b) • v = a • v + b • v := by
  sorry
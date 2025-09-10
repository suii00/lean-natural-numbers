import Mathlib.LinearAlgebra.Basic
import Mathlib.Algebra.Module.Basic

-- ゼロスカラーをかけるとゼロベクトルになる
theorem zero_scalar_mul {R V : Type*} 
  [Semiring R] [AddCommMonoid V] [Module R V]
  (v : V) : 
  (0 : R) • v = 0 := by
  sorry
  
-- ゼロベクトルに何をかけてもゼロベクトル
theorem scalar_mul_zero {R V : Type*} 
  [Semiring R] [AddCommMonoid V] [Module R V]
  (a : R) : 
  a • (0 : V) = 0 := by
  sorry
import Mathlib.LinearAlgebra.Basic

-- 線形写像の加法性の証明
theorem linear_map_add_property {R V W : Type*} 
  [Semiring R] [AddCommMonoid V] [AddCommMonoid W] 
  [Module R V] [Module R W]
  (f : V →ₗ[R] W) (v w : V) : 
  f (v + w) = f v + f w := by
  sorry
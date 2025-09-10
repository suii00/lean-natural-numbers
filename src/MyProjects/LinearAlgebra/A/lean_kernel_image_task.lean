import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Span

-- 線形写像の核が部分空間であることの証明
theorem ker_is_submodule {R V W : Type*} 
  [Semiring R] [AddCommMonoid V] [AddCommMonoid W] 
  [Module R V] [Module R W]
  (f : V →ₗ[R] W) : 
  ∀ (v w : V), v ∈ f.ker → w ∈ f.ker → (v + w) ∈ f.ker := by
  sorry

-- 線形写像の像が部分空間であることの証明  
theorem range_is_submodule {R V W : Type*}
  [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
  [Module R V] [Module R W]
  (f : V →ₗ[R] W) :
  ∀ (y z : W), y ∈ f.range → z ∈ f.range → (y + z) ∈ f.range := by
  sorry

-- 発展：核の元のスカラー倍も核に属する
theorem ker_smul_closed {R V W : Type*}
  [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
  [Module R V] [Module R W]
  (f : V →ₗ[R] W) (a : R) (v : V) :
  v ∈ f.ker → (a • v) ∈ f.ker := by
  sorry
import Mathlib.LinearAlgebra.Basic

-- 線形写像の合成の線形性
theorem comp_preserves_linearity {R U V W : Type*}
  [Semiring R] 
  [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid W]
  [Module R U] [Module R V] [Module R W]
  (g : V →ₗ[R] W) (f : U →ₗ[R] V) (u₁ u₂ : U) :
  (g ∘ₗ f) (u₁ + u₂) = (g ∘ₗ f) u₁ + (g ∘ₗ f) u₂ := by
  sorry

-- 線形写像の合成の結合法則
theorem comp_assoc {R U V W X : Type*}
  [Semiring R]
  [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
  [Module R U] [Module R V] [Module R W] [Module R X]
  (h : W →ₗ[R] X) (g : V →ₗ[R] W) (f : U →ₗ[R] V) :
  (h ∘ₗ g) ∘ₗ f = h ∘ₗ (g ∘ₗ f) := by
  sorry

-- 発展：恒等写像との合成
theorem comp_id_left {R V W : Type*}
  [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
  [Module R V] [Module R W]
  (f : V →ₗ[R] W) :
  LinearMap.id ∘ₗ f = f := by
  sorry
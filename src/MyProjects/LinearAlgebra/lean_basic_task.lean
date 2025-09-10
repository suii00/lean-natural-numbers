import Mathlib.Algebra.Module.Basic

-- ゼロスカラーをかけるとゼロベクトルになる
theorem zero_scalar_mul {R V : Type*} 
  [Semiring R] [AddCommMonoid V] [Module R V]
  (v : V) : 
  (0 : R) • v = 0 := by
  simpa using (zero_smul R v)
  
-- ゼロベクトルに何をかけてもゼロベクトル
theorem scalar_mul_zero {R V : Type*} 
  [Semiring R] [AddCommMonoid V] [Module R V]
  (a : R) : 
  a • (0 : V) = 0 := by
  simpa using (smul_zero a)

-- Bourbaki スタイルの軽い example（API の最小行使）
section Examples
  variable {R V : Type*}
  variable [Semiring R] [AddCommMonoid V] [Module R V]
  example (v : V) : (0 : R) • v = 0 := by
    simpa using (zero_smul R v)
  example (a : R) : a • (0 : V) = 0 := by
    simpa using (smul_zero a)
end Examples

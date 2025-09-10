-- 必要なimport文
import Mathlib.LinearAlgebra.Basic
import Mathlib.Algebra.Module.Basic

-- ベクトル空間における分配法則の証明
-- R: スカラーの型（実数など）
-- V: ベクトル空間の型
theorem scalar_mul_distribute {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
  (a : R) (v w : V) : a • (v + w) = a • v + a • w := by
  sorry
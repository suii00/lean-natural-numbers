import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod

-- 線形写像の加法性の証明
theorem linear_map_add_property {R V W : Type*} 
  [Semiring R] [AddCommMonoid V] [AddCommMonoid W] 
  [Module R V] [Module R W]
  (f : V →ₗ[R] W) (v w : V) : 
  f (v + w) = f v + f w := by
  simpa using (LinearMap.map_add f v w)

-- Bourbaki スタイルの軽い example：順序対と射影で成分を読み取る
section Examples
  variable {R V W : Type*}
  variable [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
  variable [Module R V] [Module R W]
  example (f : V →ₗ[R] W) (p : V × V) : f (p.1 + p.2) = f p.1 + f p.2 := by
    simpa using (LinearMap.map_add f p.1 p.2)
  example (f : V →ₗ[R] W) (v w : V) : f (v + w) = f v + f w := by
    simpa using (LinearMap.map_add f v w)
end Examples

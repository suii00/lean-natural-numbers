import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Prod

-- スカラーの和に対する分配法則
theorem scalar_add_distribute {R V : Type*} 
  [Semiring R] [AddCommMonoid V] [Module R V]
  (a b : R) (v : V) : 
  (a + b) • v = a • v + b • v := by
  simpa using (add_smul a b v)

-- Bourbaki スタイルの軽い example：直積に対して射影で成分確認
section Examples
  variable {R V W : Type*}
  variable [Semiring R]
  variable [AddCommMonoid V] [AddCommMonoid W]
  variable [Module R V] [Module R W]
  example (a b : R) (x : V × W) : ((a + b) • x).1 = a • x.1 + b • x.1 := by
    simpa using congrArg Prod.fst (add_smul a b x)
  example (a b : R) (x : V × W) : ((a + b) • x).2 = a • x.2 + b • x.2 := by
    simpa using congrArg Prod.snd (add_smul a b x)
end Examples

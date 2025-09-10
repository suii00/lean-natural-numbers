import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod

/-!
  Bourbaki の精神（順序対と射影）：
  構造は順序対とその射影 π₁, π₂ により特徴付けられる。線形写像の合成も、
  値を順序対に入れて射影で読むことで成分ごとに確認できる。
-/

noncomputable section

namespace MyProjects.LinearAlgebra.A

-- 線形写像の合成の線形性
theorem comp_preserves_linearity {R U V W : Type*}
  [Semiring R]
  [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid W]
  [Module R U] [Module R V] [Module R W]
  (g : V →ₗ[R] W) (f : U →ₗ[R] V) (u₁ u₂ : U) :
  (g.comp f) (u₁ + u₂) = (g.comp f) u₁ + (g.comp f) u₂ := by
  simpa using (LinearMap.map_add (g.comp f) u₁ u₂)

-- 線形写像の合成の結合法則
theorem comp_assoc {R U V W X : Type*}
  [Semiring R]
  [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
  [Module R U] [Module R V] [Module R W] [Module R X]
  (h : W →ₗ[R] X) (g : V →ₗ[R] W) (f : U →ₗ[R] V) :
  (h.comp g).comp f = h.comp (g.comp f) := by
  ext u; rfl

-- 発展：恒等写像との合成
theorem comp_id_left {R V W : Type*}
  [Semiring R] [AddCommMonoid V] [AddCommMonoid W]
  [Module R V] [Module R W]
  (f : V →ₗ[R] W) :
  LinearMap.id.comp f = f := by
  ext v; rfl

/-! ## Bourbaki スタイルの射影による成分チェック（例） -/

section Examples
  variable {R U V W : Type*}
  variable [Semiring R]
  variable [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid W]
  variable [Module R U] [Module R V] [Module R W]

  -- 合成の加法性を値レベル（関数合成として）で確認
  example (g : V →ₗ[R] W) (f : U →ₗ[R] V) (u₁ u₂ : U) :
      g (f (u₁ + u₂)) = g (f u₁) + g (f u₂) := by
    simpa using (LinearMap.map_add (g.comp f) u₁ u₂)

  -- 順序対値の線形写像に対して、射影で成分ごとに `map_add` を読む
  example (f : U →ₗ[R] V × W) (u₁ u₂ : U) :
      (f (u₁ + u₂)).1 = (f u₁).1 + (f u₂).1 := by
    simpa using congrArg Prod.fst (LinearMap.map_add f u₁ u₂)

  example (f : U →ₗ[R] V × W) (u₁ u₂ : U) :
      (f (u₁ + u₂)).2 = (f u₁).2 + (f u₂).2 := by
    simpa using congrArg Prod.snd (LinearMap.map_add f u₁ u₂)

  -- 結合律は成分に適用しても同じ（`ext` での等式確認）
  example (h : W →ₗ[R] W) (g : V →ₗ[R] W) (f : U →ₗ[R] V) :
      ((h.comp g).comp f) = h.comp (g.comp f) := by
    ext u; rfl
end Examples

end MyProjects.LinearAlgebra.A

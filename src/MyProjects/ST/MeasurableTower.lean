/-
Copyright (c) 2025
Authors: Structure Tower Project
-/

import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable Towers with Minimal Layers

Following the Bourbaki-inspired viewpoint from `CAT2_complete.lean`, we upgrade
structure towers so that each layer carries a σ-代数 rather than a plain set.
This yields a tower that models filtrations in probability theory more
faithfully.  The key new ingredient is the use of `MeasurableSpace.prod` in the
definition of the product tower.
-/

noncomputable section

open scoped MeasureTheory

open Set

universe u v

namespace MyProjects
namespace ST

/-- 測度論的構造塔。各層が集合ではなく `MeasurableSpace` を備えており、
    最小層は単点集合が可測になる最小の時刻を表す。 -/
structure MeasurableTowerWithMin where
  carrier : Type u
  Index : Type v
  [indexPreorder : Preorder Index]
  /-- 各層に対応する σ-代数 -/
  layer : Index → MeasurableSpace carrier
  /-- 層の包含関係（時間に沿って情報が増える） -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ≤ layer j
  /-- 各要素に対する最小可測層 -/
  minLayer : carrier → Index
  /-- 最小層で単点集合が可測 -/
  minLayer_mem : ∀ x, MeasurableSet[(layer (minLayer x))] ({x} : Set carrier)
  /-- 単点集合が可測になる任意の層は、最小層以上 -/
  minLayer_minimal :
    ∀ x i, MeasurableSet[(layer i)] ({x} : Set carrier) → minLayer x ≤ i

attribute [simp] MeasurableTowerWithMin.minLayer

/-- 添字集合には構造体が保持する半順序を自動的に与える。 -/
instance instIndexPreorder (T : MeasurableTowerWithMin.{u, v}) :
    Preorder T.Index :=
  T.indexPreorder

namespace MeasurableTowerWithMin

variable {T₁ T₂ : MeasurableTowerWithMin.{u, v}}

/-- 補助補題：σ-代数の積はそれぞれの引き上げに対して単調。 -/
lemma prod_le_prod {α β}
    {m₁ m₁' : MeasurableSpace α} {m₂ m₂' : MeasurableSpace β}
    (h₁ : m₁ ≤ m₁') (h₂ : m₂ ≤ m₂') :
    m₁.prod m₂ ≤ m₁'.prod m₂' := by
  classical
  dsimp [MeasurableSpace.prod]
  refine sup_le ?_ ?_
  · exact (le_trans (MeasurableSpace.comap_mono (g := Prod.fst) h₁) le_sup_left)
  · exact (le_trans (MeasurableSpace.comap_mono (g := Prod.snd) h₂) le_sup_right)

/-- 構造塔の直積。層の積として `MeasurableSpace.prod`（積σ-代数）を採用する。 -/
def prod (T₁ T₂ : MeasurableTowerWithMin.{u, v}) :
    MeasurableTowerWithMin.{u, v} where
  carrier := T₁.carrier × T₂.carrier
  Index := T₁.Index × T₂.Index
  indexPreorder := inferInstance
  layer := fun ⟨i, j⟩ => (T₁.layer i).prod (T₂.layer j)
  monotone := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    obtain ⟨hi, hj⟩ := h
    exact prod_le_prod (T₁.monotone hi) (T₂.monotone hj)
  minLayer := fun ⟨x, y⟩ => ⟨T₁.minLayer x, T₂.minLayer y⟩
  minLayer_mem := by
    intro ⟨x, y⟩
    have hx := T₁.minLayer_mem x
    have hy := T₂.minLayer_mem y
    have hprod :
        MeasurableSet[((T₁.layer (T₁.minLayer x)).prod
          (T₂.layer (T₂.minLayer y)))]
          (({x} : Set T₁.carrier) ×ˢ ({y} : Set T₂.carrier)) :=
      MeasurableSet.prod hx hy
    simpa [singleton_prod_singleton] using hprod
  minLayer_minimal := by
    intro ⟨x, y⟩ ⟨i, j⟩ hxy
    have hsingleton :
        MeasurableSet[((T₁.layer i).prod (T₂.layer j))]
          (({x} : Set T₁.carrier) ×ˢ ({y} : Set T₂.carrier)) := by
      simpa [singleton_prod_singleton] using hxy
    have hxhy :
        MeasurableSet[(T₁.layer i)] ({x} : Set T₁.carrier) ∧
          MeasurableSet[(T₂.layer j)] ({y} : Set T₂.carrier) := by
      classical
      have hnonempty :
          (({x} : Set T₁.carrier) ×ˢ ({y} : Set T₂.carrier)).Nonempty := by
        refine ⟨⟨x, y⟩, ?_, ?_⟩ <;> simp
      have := (measurableSet_prod_of_nonempty
        (α := T₁.carrier) (β := T₂.carrier)
        (m := T₁.layer i) (mβ := T₂.layer j)
        (s := ({x} : Set T₁.carrier)) (t := ({y} : Set T₂.carrier))
        hnonempty).1 hsingleton
      simpa using this
    exact ⟨T₁.minLayer_minimal x i hxhy.1,
      T₂.minLayer_minimal y j hxhy.2⟩

end MeasurableTowerWithMin

/-- 自明な例：自然数上で全ての層が最大σ-代数（すべての集合が可測）になる構造塔。 -/
def trivialMeasurableTowerNat : MeasurableTowerWithMin where
  carrier := ℕ
  Index := ℕ
  layer := fun _ => ⊤
  monotone := by
    intro _ _ _ s _; simp
  minLayer := fun _ => 0
  minLayer_mem := by
    intro x
    simp
  minLayer_minimal := by
    intro x i _
    exact Nat.zero_le i

/-- 例：自明な塔の自己直積での `minLayer` 計算。 -/
example :
    (MeasurableTowerWithMin.prod trivialMeasurableTowerNat
      trivialMeasurableTowerNat).minLayer ((0 : ℕ), (0 : ℕ)) =
        ((0 : ℕ), (0 : ℕ)) :=
  rfl

end ST
end MyProjects

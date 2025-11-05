import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import MyProjects.ST.MeasurableTower

/-!
# Probability Towers à la Bourbaki

We transport the filtration challenges from `Claude_Probability.md` into Lean.
Starting from the measurable tower infrastructure we:

* formalise discrete-time filtrations whose layers are measurable spaces,
* equip them with a `minLayer` via `MeasurableTowerWithMin`,
* exhibit simple constructions (trivial and product filtrations),
* and provide lightweight sanity checks.

The focus stays on small, verifiable lemmas that mirror the notebook tasks.
-/

noncomputable section

universe u v

open Classical
open Set
open scoped MeasureTheory

namespace MyProjects
namespace ST
namespace Claude

/-- A discrete filtration on `Ω` viewed through measurable structures.
Each layer `sigma n` is a σ-algebra on `Ω`, the family is monotone in `n`,
and every singleton becomes measurable at some finite stage. -/
structure DiscreteFiltration (Ω : Type u) [MeasurableSpace Ω] where
  sigma : ℕ → MeasurableSpace Ω
  adapted : ∀ {m n : ℕ}, m ≤ n → sigma m ≤ sigma n
  bounded : ∀ n, sigma n ≤ (inferInstance : MeasurableSpace Ω)
  point_measurable :
    ∀ ω : Ω, ∃ n : ℕ,
      MeasurableSet[(sigma n)] ({ω} : Set Ω)

namespace DiscreteFiltration

variable {Ω : Type u} [MeasurableSpace Ω] (F : DiscreteFiltration Ω)

/-- Monotonicity in filtration time as a handy lemma. -/
lemma mono {m n : ℕ} (hmn : m ≤ n) :
    F.sigma m ≤ F.sigma n :=
  F.adapted hmn

/-- Convert a discrete filtration into a measurable tower with a minimal layer. -/
def toMeasurableTower :
    MeasurableTowerWithMin where
  carrier := Ω
  Index := ℕ
  indexPreorder := inferInstance
  layer := F.sigma
  monotone := by
    intro i j hij
    exact F.mono hij
  minLayer := fun ω => Nat.find (F.point_measurable ω)
  minLayer_mem := by
    intro ω
    classical
    simpa using
      (@Nat.find_spec (fun n : ℕ =>
        MeasurableSet[(F.sigma n)] ({ω} : Set Ω))
        (Classical.decPred _)
        (F.point_measurable ω))
  minLayer_minimal := by
    intro ω i hi
    classical
    change Nat.find (F.point_measurable ω) ≤ i
    simpa using
      (@Nat.find_min' (fun n : ℕ =>
        MeasurableSet[(F.sigma n)] ({ω} : Set Ω))
        (Classical.decPred _)
        (F.point_measurable ω) i hi)

/-- The minimal layer chosen for `ω` indeed bounds the witness index. -/
lemma minLayer_le {ω : Ω} {i : ℕ}
    (hi : MeasurableSet[(F.sigma i)] ({ω} : Set Ω)) :
    (F.toMeasurableTower.minLayer ω) ≤ i := by
  classical
  change Nat.find (F.point_measurable ω) ≤ i
  simpa using
    (@Nat.find_min' (fun n : ℕ =>
      MeasurableSet[(F.sigma n)] ({ω} : Set Ω))
      (Classical.decPred _)
      (F.point_measurable ω) i hi)

variable (Ω : Type u) [MeasurableSpace Ω]

/-- Trivial filtration exposing every set from time zero.
We assume singletons are measurable in the ambient space. -/
def trivial [MeasurableSingletonClass Ω] :
    DiscreteFiltration Ω where
  sigma _ := (inferInstance : MeasurableSpace Ω)
  adapted := by
    intro _ _ _ s hs; simpa using hs
  bounded := by
    intro _; exact le_rfl
  point_measurable := by
    intro ω
    refine ⟨0, ?_⟩
    simpa using (measurableSet_singleton ω)

end DiscreteFiltration

section ProductFiltration

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- The product of two discrete filtrations on the product space. -/
def product (F₁ : DiscreteFiltration Ω₁) (F₂ : DiscreteFiltration Ω₂) :
    DiscreteFiltration (Ω₁ × Ω₂) where
  sigma n := (F₁.sigma n).prod (F₂.sigma n)
  adapted := by
    intro m n hmn
    simpa using
      MeasurableTowerWithMin.prod_le_prod
        (F₁.mono hmn) (F₂.mono hmn)
  bounded := by
    intro n
    simpa using
      MeasurableTowerWithMin.prod_le_prod
        (F₁.bounded n) (F₂.bounded n)
  point_measurable := by
    intro ω
    classical
    rcases ω with ⟨ω₁, ω₂⟩
    obtain ⟨n₁, h₁⟩ := F₁.point_measurable ω₁
    obtain ⟨n₂, h₂⟩ := F₂.point_measurable ω₂
    refine ⟨max n₁ n₂, ?_⟩
    have h₁' :
        MeasurableSet[(F₁.sigma (max n₁ n₂))]
          ({ω₁} : Set Ω₁) := by
      have hmono := F₁.mono (Nat.le_max_left n₁ n₂)
      simpa using
        hmono (s := ({ω₁} : Set Ω₁))
          (by simpa using h₁ :
          MeasurableSet[(F₁.sigma n₁)] ({ω₁} : Set Ω₁))
    have h₂' :
        MeasurableSet[(F₂.sigma (max n₁ n₂))]
          ({ω₂} : Set Ω₂) := by
      have hmono := F₂.mono (Nat.le_max_right n₁ n₂)
      simpa using
        hmono (s := ({ω₂} : Set Ω₂))
          (by simpa using h₂ :
          MeasurableSet[(F₂.sigma n₂)] ({ω₂} : Set Ω₂))
    have hprod :
        MeasurableSet[((F₁.sigma (max n₁ n₂)).prod
          (F₂.sigma (max n₁ n₂)))]
          (({ω₁} : Set Ω₁) ×ˢ ({ω₂} : Set Ω₂)) :=
      MeasurableSet.prod h₁' h₂'
    have hsingleton :
        ({(ω₁, ω₂)} : Set (Ω₁ × Ω₂)) =
          (({ω₁} : Set Ω₁) ×ˢ ({ω₂} : Set Ω₂)) := by
      ext x; constructor
      · intro hx
        rcases hx with rfl
        simp
      · intro hx
        rcases hx with ⟨hx₁, hx₂⟩
        have hx₁' : x.1 = ω₁ := by simpa using hx₁
        have hx₂' : x.2 = ω₂ := by simpa using hx₂
        subst hx₁'
        subst hx₂'
        simp
    have hsingleton_meas :
        MeasurableSet[((F₁.sigma (max n₁ n₂)).prod
          (F₂.sigma (max n₁ n₂)))]
          ({(ω₁, ω₂)} : Set (Ω₁ × Ω₂)) :=
      hsingleton.symm ▸ hprod
    exact hsingleton_meas

end ProductFiltration

/-- A tiny example exercising the infrastructure. -/
example (Ω : Type*) [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (ω : Ω) :
    MeasurableSet[((DiscreteFiltration.trivial (Ω := Ω)).sigma 0)]
      ({ω} : Set Ω) := by
  simpa [DiscreteFiltration.trivial] using (measurableSet_singleton ω)

/-- 今後の拡張予定:
* `naturalFiltration` — 可測過程 `X : ℕ → Ω → α` から生成される標準フィルトレーションを
  `DiscreteFiltration` として実装し、`MeasurableSpace.generateFrom` を使って各層を構成する。
* `StoppingTime` — フィルトレーションに対する停止時刻を定義し、`minLayer` との対応
  （`τ(ω) := F.toMeasurableTower.minLayer ω` が停止時刻になること）を証明する。
これらの定義と補題は `Claude_Probability.md` の課題 1・2 に対応し、今後 Lean へ移植する予定。 -/
def _futureWorkNote : Unit := ()

end Claude
end ST
end MyProjects

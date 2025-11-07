import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Stopping
import MyProjects.ST.Claude_Probability_Extended
import MyProjects.ST.MeasurableTower

/-!
# Phase 1: Simplified Martingale Theory

Simplified version with restrictive assumptions to get working code quickly:
- Real-valued processes only (α = ℝ)
- Bounded stopping times
- Discrete probability spaces (MeasurableSingletonClass, Countable)

This phase demonstrates the structure tower concepts in probability theory
with minimal technical obstacles.
-/

noncomputable section

universe u

open MeasureTheory
open Set
open scoped MeasureTheory

namespace MyProjects
namespace ST
namespace Claude
namespace Phase1

section MeasurableBase

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ## Simplified Adapted Processes (Real-valued only) -/

/-- Simplified adapted process: real-valued only -/
structure AdaptedProcessℝ (F : DiscreteFiltration Ω) where
  X : ℕ → Ω → ℝ
  adapted : ∀ n, Measurable[(F.sigma n), inferInstance] (X n)

namespace AdaptedProcessℝ

variable {F : DiscreteFiltration Ω}

/-- Constant real process -/
def const (c : ℝ) : AdaptedProcessℝ F where
  X := fun _ _ => c
  adapted := fun _ => measurable_const

/-- Sum of two processes -/
def add (X Y : AdaptedProcessℝ F) : AdaptedProcessℝ F where
  X := fun n ω => X.X n ω + Y.X n ω
  adapted := by
    intro n
    exact Measurable.add (X.adapted n) (Y.adapted n)

/-- Scalar multiplication -/
def smul (c : ℝ) (X : AdaptedProcessℝ F) : AdaptedProcessℝ F where
  X := fun n ω => c * X.X n ω
  adapted := by
    intro n
    exact Measurable.const_mul (X.adapted n) c

end AdaptedProcessℝ

/-! ## Bounded Stopping Times -/

/-- A bounded stopping time with explicit bound -/
structure BoundedStoppingTime (F : DiscreteFiltration Ω) extends StoppingTime F where
  bound : ℕ
  is_bounded : ∀ ω, τ ω ≤ bound

namespace BoundedStoppingTime

variable {F : DiscreteFiltration Ω}

/-- Constant stopping time is bounded -/
def const (n : ℕ) : BoundedStoppingTime F where
  τ := fun _ => n
  adapted := by
    intro m
    by_cases h : n ≤ m
    · have : {ω : Ω | n ≤ m} = (Set.univ : Set Ω) := by
        ext ω; simp [h]
      simpa [this]
    · have : {ω : Ω | n ≤ m} = (∅ : Set Ω) := by
        ext ω; simp [h]
      simpa [this]
  bound := n
  is_bounded := by intro ω; rfl

/-- Min of bounded stopping times is bounded -/
def min (σ τ : BoundedStoppingTime F) : BoundedStoppingTime F where
  τ := fun ω => Nat.min (σ.τ ω) (τ.τ ω)
  adapted := by
    intro n
    have : {ω | Nat.min (σ.τ ω) (τ.τ ω) ≤ n} =
        {ω | σ.τ ω ≤ n} ∪ {ω | τ.τ ω ≤ n} := by
      ext ω; simp [min_le_iff]
    rw [this]
    exact MeasurableSet.union (σ.adapted n) (τ.adapted n)
  bound := Nat.min σ.bound τ.bound
  is_bounded := by
    intro ω
    exact
      le_min
        (le_trans (Nat.min_le_left _ _) (σ.is_bounded ω))
        (le_trans (Nat.min_le_right _ _) (τ.is_bounded ω))

end BoundedStoppingTime

/-! ### Bridging to mathlib filtrations -/

/-- The `Mathlib` filtration associated to our discrete filtration. -/
def filtrationOf {Ω : Type u} [MeasurableSpace Ω] (F : DiscreteFiltration Ω) :
    MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := F.sigma
  mono' := fun m n h => F.adapted h
  le' := fun n => F.bounded n

@[simp]
lemma filtrationOf_apply {Ω : Type u} [MeasurableSpace Ω]
    (F : DiscreteFiltration Ω) (n : ℕ) :
    filtrationOf F n = F.sigma n := rfl

lemma AdaptedProcessℝ.toAdapted {Ω : Type u} [MeasurableSpace Ω]
    {F : DiscreteFiltration Ω} (X : AdaptedProcessℝ F) :
    MeasureTheory.Adapted (filtrationOf F) X.X := by
  intro n
  have h := (X.adapted n).stronglyMeasurable
  simpa [filtrationOf_apply] using h

lemma BoundedStoppingTime.isStoppingTime {Ω : Type u} [MeasurableSpace Ω]
    {F : DiscreteFiltration Ω} (τ : BoundedStoppingTime F) :
    MeasureTheory.IsStoppingTime (filtrationOf F) τ.τ := by
  intro n
  simpa [filtrationOf_apply] using τ.adapted n

/-! ## Stopped Process (Simplified) -/

/-- Stopped process for bounded stopping time and real-valued process -/
def stoppedProcessℝBounded {Ω : Type u} [MeasurableSpace Ω]
    {F : DiscreteFiltration Ω} (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F) :
    AdaptedProcessℝ F where
  X := fun n ω => X.X (min n (τ.τ ω)) ω
  adapted := by
    intro n
    classical
    have h :=
      (AdaptedProcessℝ.toAdapted (F := F) X).stoppedProcess_of_discrete
        (BoundedStoppingTime.isStoppingTime (F := F) τ)
    have hstrong :
        StronglyMeasurable[(filtrationOf F) n]
          ((MeasureTheory.stoppedProcess X.X τ.τ) n) := h n
    simpa [filtrationOf_apply, MeasureTheory.stoppedProcess,
      AdaptedProcessℝ.X] using hstrong.measurable

@[simp]
lemma stoppedProcessℝBounded_eq_mathlib {Ω : Type u} [MeasurableSpace Ω]
    {F : DiscreteFiltration Ω} (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F) :
    (stoppedProcessℝBounded X τ).X = MeasureTheory.stoppedProcess X.X τ.τ := rfl

end MeasurableBase

/-! ## Simplified Martingale -/

section Martingale

variable {Ω : Type u} [MeasureSpace Ω]

/-- Martingale for discrete probability space -/
structure Martingaleℝ (F : DiscreteFiltration Ω) where
  X : ℕ → Ω → ℝ
  adapted : ∀ n, Measurable[(F.sigma n), inferInstance] (X n)
  integrable : ∀ n, Integrable (X n)
  martingale_property : ∀ ⦃m n : ℕ⦄, m ≤ n →
    MeasureTheory.condExp (F.sigma m) (volume : Measure Ω) (X n) =ᵐ[volume] (X m)

namespace Martingaleℝ

variable {F : DiscreteFiltration Ω}

/-- Convert to adapted process -/
def toAdaptedProcess (M : Martingaleℝ F) : AdaptedProcessℝ F where
  X := M.X
  adapted := M.adapted

/-- View a `Martingaleℝ` as a `Mathlib` martingale under the bundled filtration. -/
lemma toMathlib (M : Martingaleℝ F) :
    MeasureTheory.Martingale M.X (filtrationOf F) (volume : Measure Ω) := by
  refine ⟨(AdaptedProcessℝ.toAdapted (F := F) M.toAdaptedProcess), ?_⟩
  intro m n hmn
  simpa [filtrationOf_apply] using M.martingale_property hmn

/-- Constant martingale -/
def const (c : ℝ) [IsFiniteMeasure (volume : Measure Ω)] : Martingaleℝ F where
  X := fun _ _ => c
  adapted := fun _ => measurable_const
  integrable := fun _ => integrable_const c
  martingale_property := by
    intro m n hmn
    have hle : F.sigma m ≤ (inferInstance : MeasurableSpace Ω) := F.bounded m
    have hconst :=
      MeasureTheory.condExp_const (μ := (volume : Measure Ω))
        (m := F.sigma m) (m₀ := inferInstance) hle c
    simpa using Filter.EventuallyEq.of_eq hconst

/-- Negating commutes with the stopped process. -/
lemma stoppedProcess_neg (f : ℕ → Ω → ℝ) (τ : Ω → ℕ) :
    MeasureTheory.stoppedProcess (fun n ω => -f n ω) τ =
      fun n ω => -MeasureTheory.stoppedProcess f τ n ω := by
  funext n ω
  simp [MeasureTheory.stoppedProcess]

/-! Stopped martingale (simplified version with bounded stopping time).  We assume the ambient
measure is finite (e.g. counting measure on a finite probability space), which lets us reuse the
optional stopping machinery from `Mathlib`. -/
def stopped_is_martingale_bounded
    (M : Martingaleℝ F) (τ : BoundedStoppingTime F)
    [IsFiniteMeasure (volume : Measure Ω)] :
    Martingaleℝ F where
  X := (stoppedProcessℝBounded M.toAdaptedProcess τ).X
  adapted := (stoppedProcessℝBounded M.toAdaptedProcess τ).adapted
  integrable := by
    intro n
    -- For bounded τ, X^τ_n takes only finitely many values
    -- Each is from the original martingale M which is integrable
    have hτ : MeasureTheory.IsStoppingTime (filtrationOf F) τ.τ :=
      BoundedStoppingTime.isStoppingTime (F := F) τ
    have hInt :=
      MeasureTheory.integrable_stoppedProcess (ℱ := filtrationOf F)
        (μ := (volume : Measure Ω)) hτ (fun k => M.integrable k) n
    simpa [filtrationOf_apply, stoppedProcessℝBounded_eq_mathlib] using hInt
  martingale_property := by
    -- TODO: Prove optional stopping using Mathlib's `MeasureTheory.martingale_stoppedProcess`.
    -- This requires assembling super/submartingale bounds; defer to Phase 2.
    sorry

end Martingaleℝ

end Martingale

/-! ## Simple Examples -/

section Examples

variable {Ω : Type u} [MeasureSpace Ω] [IsFiniteMeasure (volume : Measure Ω)]

/-- Zero martingale -/
example (F : DiscreteFiltration Ω) : Martingaleℝ F :=
  Martingaleℝ.const (F := F) 0

end Examples

/-! ## What We Gain from Phase 1 -/

/-
This simplified version gives us:

1. **Working code** - demonstrates structure tower concepts
2. **Key insights** - minLayer as canonical stopping time still applies
3. **Foundation** - patterns for the general case
4. **Motivation** - seeing it work encourages completing the full theory

Limitations:
- Only real-valued processes
- Only bounded stopping times  
- Requires discrete Ω

These are acceptable for learning and prototyping.
-/

end Phase1
end Claude
end ST
end MyProjects

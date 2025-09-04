/-
  Bourbaki Topology B — Section C (Stone–Čech integration)

  This file provides a small, stable wrapper `StoneCechCompactification X`
  whose data and universal property are realized by mathlib's `StoneCech X`.
  It is intentionally self‑contained so it can be compiled independently of
  other sections (A, A', B) that may be under active editing.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactification.StoneCech

namespace Bourbaki.TopologyB

/-!
## Abstract packaging of βX with its universal property

`StoneCechCompactification X` stores:
- a carrier type `βX` with instances `[TopologicalSpace] [CompactSpace] [T2Space]`,
- the unit map `ι : ContinuousMap X βX`, dense range,
- and the universal property as an existence/uniqueness of extensions.

We then provide:
- `lift` from the universal property with `simp` lemmas,
- a trivial instance for compact Hausdorff `X`,
- a mathlib‑backed instance via `StoneCech X`.
!-/

universe u v

variable (X : Type u) [TopologicalSpace X]

structure StoneCechCompactification where
  βX : Type v
  instTopβX : TopologicalSpace βX
  instCompβX : CompactSpace βX
  instT2βX : T2Space βX
  ι : ContinuousMap X βX
  dense_range : DenseRange ι
  universal :
    ∀ (K : Type v) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K)
      (f : ContinuousMap X K),
      ∃ F : ContinuousMap βX K, F.comp ι = f ∧ ∀ G, G.comp ι = f → G = F

attribute [instance] StoneCechCompactification.instTopβX
attribute [instance] StoneCechCompactification.instCompβX
attribute [instance] StoneCechCompactification.instT2βX

namespace StoneCechCompactification

variable {X}

noncomputable def lift
    (S : StoneCechCompactification (X := X))
    (K : Type v) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) : ContinuousMap S.βX K :=
  (S.universal K _ _ _ f).choose

@[simp] lemma lift_comp
    (S : StoneCechCompactification (X := X))
    (K : Type v) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) :
    (S.lift K f).comp S.ι = f := by
  classical
  exact (S.universal K _ _ _ f).choose_spec.left

@[simp] lemma lift_comp_apply
    (S : StoneCechCompactification (X := X))
    (K : Type v) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) (x : X) :
    ((S.lift K f).comp S.ι) x = f x := by
  classical
  simpa using congrArg (fun (h : ContinuousMap X K) => h x) (S.lift_comp (K := K) f)

lemma lift_unique
    (S : StoneCechCompactification (X := X))
    (K : Type v) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) {G : ContinuousMap S.βX K}
    (hG : G.comp S.ι = f) :
    G = S.lift K f := by
  classical
  rcases (S.universal K _ _ _ f) with ⟨F, hcomp, huniq⟩
  have : G = F := huniq _ hG
  simpa [this]

/-! ### Trivial compactification when `X` is already compact Hausdorff -!/

noncomputable def trivial
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    StoneCechCompactification (X := X) :=
{ βX := X
, instTopβX := inferInstance
, instCompβX := inferInstance
, instT2βX := inferInstance
, ι := ContinuousMap.id X
, dense_range := by
    classical
    simpa using (denseRange_id : DenseRange (fun x : X => x))
, universal := by
    intro K _ _ _ f
    exact ⟨f, by ext x <;> rfl, by intro G hG; ext x; simpa using congrArg (fun (h : ContinuousMap X K) => h x) hG⟩ }

end StoneCechCompactification

/-! ## Integration with mathlib's `StoneCech` -!/

section FromMathlib

variable {X}

noncomputable def StoneCechCompactification.fromMathlib
    (X : Type u) [TopologicalSpace X] :
    StoneCechCompactification (X := X) :=
{ βX := StoneCech X
, instTopβX := inferInstance
, instCompβX := inferInstance
, instT2βX := inferInstance
, ι := ⟨stoneCechUnit, continuous_stoneCechUnit⟩
, dense_range := by
    simpa using (denseRange_stoneCechUnit : DenseRange (stoneCechUnit : X → StoneCech X))
, universal := by
    intro K _ _ _ f
    classical
    -- existence via `stoneCechExtend`
    refine ⟨
      ⟨stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous,
        continuous_stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous⟩,
      ?comp, ?uniq⟩
    · -- β-rule: extension comp unit = original
      -- use function-level lemma and upgrade to bundled equality by `ext`
      have hfun := stoneCechExtend_extends (α := X) (β := K)
        (g := fun x => f x) (hg := f.continuous)
      ext x; simpa [Function.comp] using congrArg (fun (h : X → K) => h x) hfun
    · -- uniqueness by density + T₂ (mathlib lemma `stoneCech_hom_ext`)
      intro G hG
      -- show equality as functions and then ext
      have hfun : (fun y => (G y)) =
                  (fun y => (⟨stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous,
                                      continuous_stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous⟩) y) := by
        -- Both sides agree on the dense range of `stoneCechUnit`.
        -- Use the β-rule to rewrite the right side after precomposition.
        apply stoneCech_hom_ext (α := X) (β := K)
        intro x; -- equality on the image of the unit
        -- from `hG` and the β-rule calculated above
        have hβ : (⟨stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous,
                       continuous_stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous⟩)
                   (stoneCechUnit x) = f x := by
          -- same computation as in `?comp` but pointwise
          have h := stoneCechExtend_extends (α := X) (β := K)
            (g := fun x => f x) (hg := f.continuous)
          simpa [Function.comp] using congrArg (fun (h : X → K) => h x) h
        -- turn `hG : G.comp ι = f` into a pointwise statement
        have hGpt : G (stoneCechUnit x) = f x := by
          have := congrArg (fun (h : ContinuousMap X K) => h x) hG
          simpa [Function.comp] using this
        simpa [hGpt, hβ]
      ext y; simpa using congrArg (fun h => h y) hfun }

end FromMathlib

/-! ### Smoke test -!/

section Smoke

variable {X} (X : Type u) [TopologicalSpace X]

example {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) (x : X) :
  ((StoneCechCompactification.fromMathlib (X := X)).lift K f).comp
      (StoneCechCompactification.fromMathlib (X := X)).ι x = f x := by
  simpa using
    (StoneCechCompactification.lift_comp_apply
      (S := StoneCechCompactification.fromMathlib (X := X)) (K := K) f x)

end Smoke

end Bourbaki.TopologyB


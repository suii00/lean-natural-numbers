/-
  Skeleton plan for future work around Bourbaki-style product/projection structuring.

  Covers three threads:
  1) Import unification from other Topology modules
  2) Product universality (diagram) lemma templates
  3) Example stubs for topological groups (usage patterns)
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.Real

import MyProjects.Topology.BourbakiProductAndHom

namespace Bourbaki.Skeleton

/-
  1) Import unification

  Suggested changes (to be applied in their respective files):
  - In `src/MyProjects/Topology/ContinuousComposition.lean` add:
      `import MyProjects.Topology.BourbakiProductAndHom`
  - In `src/MyProjects/Topology/FilterContinuity.lean` add:
      `import MyProjects.Topology.BourbakiProductAndHom`
  - In `src/MyProjects/Topology/FundamentalGroupFunctor.lean` add:
      `import MyProjects.Topology.BourbakiProductAndHom`

  This file is only a staging area; it does not change those files yet.
-/

section ProductUniversalityTemplates

variable {T X Y : Type*}
variable [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

-- TODO: Prove the universal property equivalence for the product topology.
-- Template (to be proved later):
-- theorem continuous_iff_proj_continuous (h : T → X × Y) :
--     Continuous h ↔ Continuous (fun t => (h t).1) ∧ Continuous (fun t => (h t).2) :=
-- by
--   -- outline:
--   --  - (→) follows from composing with `continuous_fst` and `continuous_snd`.
--   --  - (←) use `Continuous.prodMk` with the two components.
--   admit

-- Minimal working placeholder example using the existing `continuous_prod_map`:
example {Z W : Type*}
    [TopologicalSpace Z] [TopologicalSpace W]
    {f : X → Z} {g : Y → W}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => (f p.1, g p.2)) :=
  Bourbaki.continuous_prod_map hf hg

end ProductUniversalityTemplates

section RealProductExample

-- Concrete instance on ℝ × ℝ using identity maps as a sanity check.
example : Continuous (fun p : ℝ × ℝ => (p.1, p.2)) :=
  Bourbaki.continuous_prod_map (X:=ℝ) (Y:=ℝ) (Z:=ℝ) (W:=ℝ)
    continuous_id continuous_id

end RealProductExample

section TopologicalGroupExamples

variable {G H : Type*}
variable [TopologicalSpace G] [Group G]
variable [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

-- Skeleton usage: continuity of inverse after a continuous hom into a topological group.
variable (f : G →* H) (hf : Continuous f)

example : Continuous (fun g : G => (f g)⁻¹) :=
  Bourbaki.topological_group_hom_continuous_inv f hf

-- TODO: Later, add a concrete instance once a convenient `H` is fixed
-- (e.g., a known multiplicative topological group in mathlib with easy homs).

end TopologicalGroupExamples

end Bourbaki.Skeleton


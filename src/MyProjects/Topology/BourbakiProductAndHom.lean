/-
  Bourbaki-style structuration via ordered pairs and projections

  Focus:
  - Product topology via projections (π₁, π₂)
  - Continuity of the induced product map (f × g)
  - Composition of group homomorphisms
  - Continuity interactions in topological groups

  References:
  - Nicolas Bourbaki, Éléments de mathématique
    Livre I (Théorie des ensembles), ordered pairs and maps
    Livre III (Topologie générale), product topology and projections
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Basic

namespace Bourbaki

section ProductTopology

variable {X Y Z W : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

/-
  Projections (morphisms) π₁, π₂ from the product X × Y.
  In Bourbaki’s spirit, these encode the structure of ordered pairs
  and generate the product topology as the coarsest making them continuous.
-/
def π₁ : X × Y → X := fun p => p.1
def π₂ : X × Y → Y := fun p => p.2

lemma continuous_π₁ : Continuous (π₁ : X × Y → X) := by
  simpa using continuous_fst

lemma continuous_π₂ : Continuous (π₂ : X × Y → Y) := by
  simpa using continuous_snd

/-
  Continuous product (f × g): if f and g are continuous, then
  the map X × Y → Z × W given by p ↦ (f p.1, g p.2) is continuous.
  This packages the universal property: continuity tested via projections.
-/
theorem continuous_prod_map {f : X → Z} {g : Y → W}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => (f p.1, g p.2)) := by
  -- Compose with projections and use `Continuous.prod_mk`.
  have hf' : Continuous (fun p : X × Y => f p.1) := hf.comp continuous_fst
  have hg' : Continuous (fun p : X × Y => g p.2) := hg.comp continuous_snd
  simpa using hf'.prodMk hg'

/-
  As small corollaries, the projections of the product map are continuous.
  These follow immediately by composing with `continuous_fst`/`continuous_snd`.
-/
lemma continuous_fst_of_prod_map {f : X → Z} {g : Y → W}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => (f p.1, g p.2).1) := by
  simpa using (continuous_fst.comp (continuous_prod_map (X:=X) (Y:=Y) (Z:=Z) (W:=W) hf hg))

lemma continuous_snd_of_prod_map {f : X → Z} {g : Y → W}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => (f p.1, g p.2).2) := by
  simpa using (continuous_snd.comp (continuous_prod_map (X:=X) (Y:=Y) (Z:=Z) (W:=W) hf hg))

end ProductTopology

section GroupHom

variable {G H K : Type*}
variable [Group G] [Group H] [Group K]

/-
  Composition of group homomorphisms (implemented as `MonoidHom` in mathlib).
-/
def groupHomComp (φ : G →* H) (ψ : H →* K) : G →* K :=
  ψ.comp φ

@[simp] lemma groupHomComp_apply (φ : G →* H) (ψ : H →* K) (g : G) :
    groupHomComp φ ψ g = ψ (φ g) := rfl

end GroupHom

section TopologicalGroup

variable {G H : Type*}
variable [TopologicalSpace G] [Group G]
variable [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

/-
  If f : G →* H is continuous, then g ↦ f (g⁻¹) is continuous.
  This is continuity of inversion (a structural morphism) followed by f.
-/
theorem topological_group_hom_continuous_inv
    (f : G →* H) (hf : Continuous f) :
    Continuous (fun g : G => (f g)⁻¹) := by
  -- inv on H is continuous; compose with f
  simpa using (continuous_inv.comp hf : Continuous fun g : G => (f g)⁻¹)

end TopologicalGroup

end Bourbaki

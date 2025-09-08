/-
  Bourbaki-style: ordered pairs, projections, and morphisms

  This module follows the spirit of Nicolas Bourbaki's Elements of Mathematics:
  structures carried by sets, ordered pairs characterized via projections (π₁, π₂),
  and morphisms checked by their behavior under these projections.

  Contents (Tasks A–C):
  A. Product topology — continuity of the induced product map (f × g)
  B. Group homomorphisms — composition as a morphism in the category of groups
  C. Topological groups — continuity under inversion (pre/post composition)
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousFunction.Basic

noncomputable section

namespace MyProjects.Topology.C

open scoped Topology

-- Core equivalence placed early for use in subsequent lemmas.
section ProductUPCore

variable {T X Y : Type*}
variable [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_iff_proj_core {h : T → X × Y} :
    Continuous h ↔ (Continuous fun t => (h t).1) ∧ (Continuous fun t => (h t).2) := by
  constructor
  · intro hh
    exact ⟨continuous_fst.comp hh, continuous_snd.comp hh⟩
  · intro hproj
    rcases hproj with ⟨h₁, h₂⟩
    simpa using h₁.prodMk h₂

end ProductUPCore

/-! # Ordered pairs and projections

In Bourbaki's viewpoint, the ordered pair (x, y) is determined by its projections
π₁, π₂. The product topology on X × Y is the coarsest topology making these
projections continuous, so continuity of maps into products can be checked
componentwise via π₁, π₂.
-/

section ProductTopology

variable {X Y Z W : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

/-- First projection π₁ : X × Y → X. -/
def π₁ : X × Y → X := fun p => p.1

/-- Second projection π₂ : X × Y → Y. -/
def π₂ : X × Y → Y := fun p => p.2

@[simp] lemma π₁_apply (p : X × Y) : π₁ p = p.1 := rfl
@[simp] lemma π₂_apply (p : X × Y) : π₂ p = p.2 := rfl

lemma continuous_π₁ : Continuous (π₁ : X × Y → X) := by simpa using continuous_fst
lemma continuous_π₂ : Continuous (π₂ : X × Y → Y) := by simpa using continuous_snd

/--
Task A. If `f : X → Z` and `g : Y → W` are continuous, then the induced product
map `X × Y → Z × W, p ↦ (f p.1, g p.2)` is continuous. This is the universal
property of products expressed via projections.
-/
@[continuity]
theorem continuous_pair_mk {f : X → Z} {g : Y → W}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => (f p.1, g p.2)) := by
  -- Use the universal property: continuity is equivalent to continuity of projections.
  have hfproj : Continuous (fun p : X × Y => (f p.1, g p.2).1) := by
    simpa using (hf.comp continuous_fst)
  have hgproj : Continuous (fun p : X × Y => (f p.1, g p.2).2) := by
    simpa using (hg.comp continuous_snd)
  exact (continuous_iff_proj_core (h := fun p : X × Y => (f p.1, g p.2))).2 ⟨hfproj, hgproj⟩

-- Quick sanity checks (do not export public API)
section Examples
  variable {f : X → Z} {g : Y → W}
  example (hf : Continuous f) (hg : Continuous g) :
      Continuous (fun p : X × Y => (f p.fst, g p.snd)) :=
    by simpa using continuous_pair_mk (X:=X) (Y:=Y) (Z:=Z) (W:=W) hf hg
  example : Continuous (fun p : X × Y => (p.1, p.2)) := by
    continuity
end Examples

end ProductTopology

/-! # Universal property via projections

For a map into a product, continuity is equivalent to continuity of its
compositions with the projections. This encodes Bourbaki’s “ordered pair is
read by its projections” principle as an equivalence.
-/

section ProductUP

variable {T X Y : Type*}
variable [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

/-- Continuity into a product is equivalent to continuity of both projections. -/
theorem continuous_iff_proj {h : T → X × Y} :
    Continuous h ↔ (Continuous fun t => (h t).1) ∧ (Continuous fun t => (h t).2) := by
  simpa using (continuous_iff_proj_core (h:=h))

/-- One-sided version: if both projections are continuous, then `h` is continuous.
    Kept separate to avoid `simp` loops with the equivalence. -/
theorem continuous_of_proj {h : T → X × Y}
    (h₁ : Continuous fun t => (h t).1) (h₂ : Continuous fun t => (h t).2) :
    Continuous h :=
  (continuous_iff_proj (h:=h)).2 ⟨h₁, h₂⟩

/-- One-sided version: continuity implies continuity of the first projection. -/
theorem continuous_proj_fst {h : T → X × Y}
    (hh : Continuous h) : Continuous (fun t => (h t).1) :=
  continuous_fst.comp hh

/-- One-sided version: continuity implies continuity of the second projection. -/
theorem continuous_proj_snd {h : T → X × Y}
    (hh : Continuous h) : Continuous (fun t => (h t).2) :=
  continuous_snd.comp hh

/-- Bridge for `Prod.map`: continuity from componentwise continuity. -/
@[continuity]
theorem continuous_Prod_map {X Y Z W : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W]
    {f : X → Z} {g : Y → W}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (Prod.map f g) := by
  -- Use the universal property directly on `h := Prod.map f g`.
  apply (continuous_iff_proj_core (h := Prod.map f g)).2
  constructor
  · -- first projection continuous
    simpa [Prod.map] using (hf.comp continuous_fst)
  · -- second projection continuous
    simpa [Prod.map] using (hg.comp continuous_snd)

/-- Normalization: composition of `Prod.map` equals `Prod.map` of compositions. -/
@[simp]
theorem prod_map_comp
    {A B C D E F : Type*}
    (f₁ : A → B) (g₁ : C → D) (f₂ : B → E) (g₂ : D → F) :
    (Prod.map f₂ g₂) ∘ (Prod.map f₁ g₁) =
      (Prod.map (f₂ ∘ f₁) (g₂ ∘ g₁)) := by
  funext p; cases p with
  | _ a c =>
    simp [Function.comp, Prod.map]

/-- Normalization: `Prod.map` with identities is the identity. -/
@[simp]
theorem prod_map_id_id {X Y : Type*} :
    Prod.map (id : X → X) (id : Y → Y) = (id : X × Y → X × Y) := by
  funext p; cases p with
  | _ x y => simp [Prod.map]

end ProductUP

/-! # Triangle identities (componentwise)

Right-triangle style identities for products, stated componentwise as function
equalities. These are convenient `simp` targets and make `by continuity` flow
through compositions with projections and `Prod.map`.
-/

section ProductTriangles

variable {T X Y Z W : Type*}

/-- Componentwise identity: composing with the first projection undoes pairing. -/
@[simp] theorem fst_comp_pair (f : T → X) (g : T → Y) :
    (fun t => ((f t, g t)).1) = f := by
  funext t; rfl

/-- Componentwise identity: composing with the second projection undoes pairing. -/
@[simp] theorem snd_comp_pair (f : T → X) (g : T → Y) :
    (fun t => ((f t, g t)).2) = g := by
  funext t; rfl

/-- Componentwise normalization for `Prod.map` and `fst`. -/
@[simp] theorem fst_comp_Prod_map (f : X → Z) (g : Y → W) :
    (Prod.fst ∘ Prod.map f g) = (f ∘ Prod.fst) := by
  funext p; cases p with
  | _ x y => simp [Function.comp, Prod.map]

/-- Componentwise normalization for `Prod.map` and `snd`. -/
@[simp] theorem snd_comp_Prod_map (f : X → Z) (g : Y → W) :
    (Prod.snd ∘ Prod.map f g) = (g ∘ Prod.snd) := by
  funext p; cases p with
  | _ x y => simp [Function.comp, Prod.map]

end ProductTriangles

/-! # ContinuousMap bridge

ContinuousMap 版の `prodMap` を最小実装。`_apply` は `rfl` で揃います。
-/

section ContinuousMapBridge

variable {X Y Z W : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

namespace ContinuousMap

def prodMap (f : ContinuousMap X Z) (g : ContinuousMap Y W) :
    ContinuousMap (X × Y) (Z × W) where
  toFun := fun p => (f p.1, g p.2)
  continuous_toFun := by
    have hf : Continuous (fun p : X × Y => f p.1) := f.continuous.comp continuous_fst
    have hg : Continuous (fun p : X × Y => g p.2) := g.continuous.comp continuous_snd
    exact (MyProjects.Topology.C.continuous_of_proj (h:=fun p : X × Y => (f p.1, g p.2)))
      (by simpa using hf) (by simpa using hg)

@[simp] lemma prodMap_apply (f : ContinuousMap X Z) (g : ContinuousMap Y W)
    (p : X × Y) : prodMap f g p = (f p.1, g p.2) := rfl

end ContinuousMap

end ContinuousMapBridge

/-! # Group morphisms

In Bourbaki's structural approach, morphisms between groups compose to yield a
group morphism again; categorically, this is just composition of arrows.
-/

section GroupHom

variable {G H K : Type*}
variable [Group G] [Group H] [Group K]

/-- Task B. Composition of group homomorphisms (implemented as `MonoidHom`). -/
def groupHomComp (φ : G →* H) (ψ : H →* K) : G →* K :=
  ψ.comp φ

@[simp] lemma groupHomComp_apply (φ : G →* H) (ψ : H →* K) (g : G) :
    groupHomComp φ ψ g = ψ (φ g) := rfl

@[simp] lemma groupHomComp_eq_comp (φ : G →* H) (ψ : H →* K) :
    groupHomComp φ ψ = ψ.comp φ := rfl

-- Left identity (id on the domain of ψ): ψ ∘ id_G = ψ
@[simp] lemma groupHomComp_id_left (ψ : G →* K) :
    groupHomComp (G:=G) (H:=G) (K:=K) (MonoidHom.id G) ψ = ψ := by
  ext g; simp [groupHomComp]

-- Variant with `G := H` (often triggered by type inference on `ψ : H →* K`).
@[simp] lemma groupHomComp_id_left' (ψ : H →* K) :
    groupHomComp (G:=H) (H:=H) (K:=K) (MonoidHom.id H) ψ = ψ := by
  ext g; simp [groupHomComp]

-- Right identity specialized (codomain equals H): ψ = id_H ∘ φ
@[simp] lemma groupHomComp_id_right (φ : G →* H) :
    groupHomComp (G:=G) (H:=H) (K:=H) φ (MonoidHom.id H) = φ := by
  ext g; simp [groupHomComp]

section TopologyBridge
  variable [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
  /-- Bridge: continuity of the underlying function of `groupHomComp`. -/
  @[continuity]
  theorem continuous_groupHomComp
      (φ : G →* H) (ψ : H →* K)
      (hf : Continuous φ) (hg : Continuous ψ) :
      Continuous (fun g : G => groupHomComp φ ψ g) := by
    simpa [groupHomComp] using (hg.comp hf : Continuous fun g : G => ψ (φ g))

  -- doctest: continuity tactic uses the bridge
  example (φ : G →* H) (ψ : H →* K)
      (hf : Continuous φ) (hg : Continuous ψ) :
      Continuous fun g : G => ψ (φ g) := by
    continuity
end TopologyBridge

-- Example: pointwise simplification
section Examples
  variable (φ : G →* H) (ψ : H →* K) (g : G)
  example : groupHomComp φ ψ g = ψ (φ g) := by simpa using groupHomComp_apply φ ψ g
end Examples

end GroupHom

/-! # Topological groups and inversion

Two Bourbaki-flavoured continuity principles around inversion for a continuous
homomorphism `f : G →* H` between topological groups.
-/

section TopologicalGroup

variable {G H : Type*}
variable [TopologicalSpace G] [Group G]
variable [TopologicalSpace H] [Group H]

section PrecomposeInv
  variable [IsTopologicalGroup G]
  /-- Pre-compose with inversion on the domain. -/
  @[continuity]
  theorem topological_group_hom_continuous_precomp_inv
      (f : G →* H) (hf : Continuous f) :
      Continuous (fun g : G => f (g⁻¹)) := by
    exact hf.comp (continuous_inv : Continuous fun g : G => g⁻¹)
end PrecomposeInv

section PostcomposeInv
  variable [IsTopologicalGroup H]
  /-- Post-compose with inversion on the codomain. -/
  @[continuity]
  theorem topological_group_hom_continuous_postcomp_inv
      (f : G →* H) (hf : Continuous f) :
      Continuous (fun g : G => (f g)⁻¹) := by
    exact (continuous_inv.comp hf : Continuous fun g : G => (f g)⁻¹)

  /-- Compatibility alias with earlier naming in notes. -/
  theorem topological_group_hom_continuous_inv
      (f : G →* H) (hf : Continuous f) :
      Continuous (fun g : G => (f g)⁻¹) :=
    topological_group_hom_continuous_postcomp_inv f hf

  -- Minimal examples to exercise the API (remain local to this section)
  section Examples
    variable (f : G →* H)
    example (hf : Continuous f) : Continuous (fun g : G => (f g)⁻¹) :=
      topological_group_hom_continuous_postcomp_inv f hf
    -- continuity tactic doctest
    example (hf : Continuous f) : Continuous fun g : G => (f g)⁻¹ := by
      continuity
  end Examples
end PostcomposeInv

end TopologicalGroup

end MyProjects.Topology.C

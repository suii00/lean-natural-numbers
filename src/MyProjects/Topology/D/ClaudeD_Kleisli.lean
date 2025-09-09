/-
  Minimal Kleisli normalization for `productMonad` (Δ ⊣ ×).
  - Stays entirely inside the Kleisli category; no mixing with TopCat arrows.
  - Uses definitional (`rfl`) lemmas so `ext; simp [Category.assoc]` cooperates
    with the η/μ component lemmas in ClaudeD.
-/

import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Kleisli
import MyProjects.Topology.D.ClaudeD

noncomputable section

namespace MyProjects.Topology.D

open CategoryTheory

/-- In `Kleisli productMonad`, the identity is definitional `η`. -/
@[simp] lemma kleisli_id_def (X : CategoryTheory.Kleisli productMonad) :
  (𝟙 X : X ⟶ X) = productMonad.η.app X := rfl

-- Kleisli composition is definitional: `f ≫ g = f ≫ T.map g ≫ μ`.
-- Composition in `Kleisli productMonad` is definitional:
-- `(f ≫ g : X ⟶ Z) = f ≫ productMonad.map g ≫ productMonad.μ.app Z`.
-- We omit a lemma here to avoid mixing notations; use this equality by `rfl`.

end MyProjects.Topology.D

/-
  ブルバキ流代数構造論
  群の第一同型定理
  
  Nicolas Bourbaki "Éléments de mathématique" 
  - Livre I: Théorie des ensembles, Chapitre II: Éléments de la théorie des ensembles
  - Livre II: Algèbre, Chapitre I: Structures algébriques
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic

namespace BourbakiAlgebra

section BourbakiDefinitions

/-- 群の公理的定義（ブルバキ第1巻第3章）-/
class BourbakiGroup (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

/-- 群準同型の定義 -/
structure BourbakiGroupHom (G H : Type*) [BourbakiGroup G] [BourbakiGroup H] where
  toFun : G → H
  map_mul' : ∀ a b : G, toFun (a * b) = toFun a * toFun b

/-- 核の定義 -/
def BourbakiGroupHom.ker {G H : Type*} [BourbakiGroup G] [BourbakiGroup H] 
    (f : BourbakiGroupHom G H) : Set G :=
  {g : G | f.toFun g = 1}

/-- 像の定義 -/
def BourbakiGroupHom.range {G H : Type*} [BourbakiGroup G] [BourbakiGroup H] 
    (f : BourbakiGroupHom G H) : Set H :=
  {h : H | ∃ g : G, f.toFun g = h}

end BourbakiDefinitions

section MathlibVersion

open QuotientGroup

/-- Mathlib版：第一同型定理 -/
theorem first_isomorphism_theorem_mathlib {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : 
    Nonempty (G ⧸ MonoidHom.ker φ ≃* MonoidHom.range φ) := by
  exact ⟨quotientKerEquivRange φ⟩

/-- 手動証明版：第一同型定理の構成的証明 -/
theorem first_isomorphism_theorem_constructive {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : 
    ∃ (ψ : G ⧸ MonoidHom.ker φ →* MonoidHom.range φ), Function.Bijective ψ := by
  -- 商群から像への写像を構成
  use QuotientGroup.rangeKerLift φ
  constructor
  -- 単射性
  · exact QuotientGroup.rangeKerLift_injective φ
  -- 全射性  
  · exact QuotientGroup.rangeKerLift_surjective φ

/-- 詳細証明版：第一同型定理の要素ごとの証明 -/
theorem first_isomorphism_theorem_detailed {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : 
    ∃ (ψ : G ⧸ MonoidHom.ker φ → MonoidHom.range φ),
      (∀ x y, ψ (x * y) = ψ x * ψ y) ∧ 
      Function.Injective ψ ∧ 
      Function.Surjective ψ := by
  -- 写像の構成
  use fun q => QuotientGroup.rangeKerLift φ q
  constructor
  -- 準同型性
  · intro x y
    exact map_mul (QuotientGroup.rangeKerLift φ) x y
  constructor
  -- 単射性
  · exact QuotientGroup.rangeKerLift_injective φ
  -- 全射性
  · exact QuotientGroup.rangeKerLift_surjective φ

end MathlibVersion

section BourbakiProof

/-- ブルバキ流証明：商集合による構成 -/
theorem bourbaki_first_isomorphism {G H : Type*} [Group G] [Group H]
    (φ : G →* H) :
    ∃ (ψ : G ⧸ MonoidHom.ker φ →* MonoidHom.range φ),
      Function.Bijective ψ := by
  -- 同値関係による商集合の構成
  -- φ(g₁) = φ(g₂) ⟺ g₁⁻¹ * g₂ ∈ ker φ
  -- この同値関係により G を分割
  
  -- 商群から像への自然な写像を定義
  use QuotientGroup.rangeKerLift φ
  
  -- 写像の well-defined 性は rangeKerLift の構成により保証
  
  -- 単射性：[g₁] = [g₂] ⟹ φ(g₁) = φ(g₂) は同値関係の定義から
  -- 全射性：任意の h ∈ range φ に対し、∃g, φ(g) = h より [g] が逆像
  
  exact ⟨QuotientGroup.rangeKerLift_injective φ, QuotientGroup.rangeKerLift_surjective φ⟩

end BourbakiProof

end BourbakiAlgebra
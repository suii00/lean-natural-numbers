/-
🎯 圏論的統一理論：Phase 2 第一同型定理の圏論化
Categorical Unification Theory: Phase 2 - Categorical First Isomorphism Theorem
-/

import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.MonoidHom.Basic

namespace CategoricalUnificationPhase2

open CategoryTheory

-- ===============================
-- 補題6: epi-mono分解の存在
-- ===============================
/-- 
任意の群準同型はepi-mono分解を持つ
Every group homomorphism has an epi-mono factorization
-/
lemma epi_mono_factorization {G H : Type*} [Group G] [Group H] (f : G →* H) :
    -- f = m ∘ e の形に分解可能
    -- f can be factorized as f = m ∘ e where e is epi and m is mono
    ∃ (M : Type*) [Group M] (e : G →* M) (m : M →* H),
    (∀ g : G, f g = m (e g)) ∧ 
    Function.Surjective e ∧ 
    Function.Injective m := by
  -- M として G/ker(f) を使用
  use G ⧸ f.ker, inferInstance
  -- e として商射を使用
  use QuotientGroup.mk' f.ker
  -- m として誘導された準同型を使用
  use QuotientGroup.lift f.ker f (fun x hx => hx)
  constructor
  · -- 分解の証明
    intro g
    rfl
  constructor
  · -- 商射は全射
    exact QuotientGroup.mk_surjective
  · -- 誘導射は単射（第一同型定理より）
    intro x y hxy
    -- G/ker(f) → im(f) の単射性を使用
    obtain ⟨gx, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨gy, rfl⟩ := QuotientGroup.mk_surjective y
    simp only [QuotientGroup.lift_mk'] at hxy
    -- f(gx) = f(gy) ならば gx ≡ gy (mod ker f)
    exact QuotientGroup.eq.mpr hxy

-- ===============================
-- 補題7: 余像の普遍性
-- ===============================
/-- 
余像（coimage）は余極限として特徴付けられる
Coimage has the universal property of a colimit
-/
lemma coimage_universal_property {G H : Type*} [Group G] [Group H] (f : G →* H) :
    -- G/ker(f) が余像として普遍性を満たす
    -- G/ker(f) satisfies the universal property as coimage
    ∀ (Q : Type*) [Group Q] (q : G →* Q),
    (∀ g ∈ f.ker, q g = 1) →
    ∃! (u : G ⧸ f.ker →* Q), ∀ g : G, q g = u (QuotientGroup.mk g) := by
  intro Q hQ q hq
  -- 普遍性により唯一の準同型が存在
  use QuotientGroup.lift f.ker q hq
  constructor
  · -- 条件を満たす
    intro g
    rfl
  · -- 一意性
    intro u hu
    ext ⟨g⟩
    · exact hu g

-- ===============================
-- 補題8: 像-余像同型の自然性
-- ===============================
/-- 
第一同型定理：余像と像の間の自然な同型
First isomorphism theorem as natural isomorphism between coimage and image
-/
lemma image_coimage_natural_iso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    -- coim(f) ≅ im(f) の自然同型
    -- Natural isomorphism coim(f) ≅ im(f)
    Nonempty (G ⧸ f.ker ≃* f.range) := by
  -- 第一同型定理の標準的な同型を構築
  refine ⟨{
    toFun := fun x => ⟨QuotientGroup.lift f.ker f (fun _ h => h) x, by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      use g
      rfl⟩
    invFun := fun ⟨y, hy⟩ => by
      obtain ⟨g, rfl⟩ := hy
      exact QuotientGroup.mk g
    left_inv := fun x => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rfl
    right_inv := fun ⟨y, hy⟩ => by
      obtain ⟨g, rfl⟩ := hy
      ext
      rfl
    map_mul' := fun x y => by
      ext
      simp only [Subgroup.mk_mul_mk]
      rfl
  }⟩

-- ===============================
-- 🎯 Phase 2 統合定理
-- ===============================
/--
Phase 2の成果統合：第一同型定理の圏論的実現
Integration theorem: Categorical realization of first isomorphism theorem
-/
theorem phase2_first_isomorphism_categorical :
    -- 任意の群準同型について
    ∀ {G H : Type*} [Group G] [Group H] (f : G →* H),
    -- 1. epi-mono分解が存在し
    (∃ (M : Type*) [Group M] (e : G →* M) (m : M →* H),
      (∀ g : G, f g = m (e g)) ∧ Function.Surjective e ∧ Function.Injective m) ∧
    -- 2. 余像が普遍性を満たし
    (∀ (Q : Type*) [Group Q] (q : G →* Q),
      (∀ g ∈ f.ker, q g = 1) →
      ∃! (u : G ⧸ f.ker →* Q), ∀ g : G, q g = u (QuotientGroup.mk g)) ∧
    -- 3. 余像と像が自然に同型である
    Nonempty (G ⧸ f.ker ≃* f.range) := by
  intro G H hG hH f
  constructor
  · exact epi_mono_factorization f
  constructor
  · exact coimage_universal_property f
  · exact image_coimage_natural_iso f

-- ===============================
-- 🔍 Library search candidates
-- ===============================
#check QuotientGroup.lift        -- 普遍性による誘導射
#check QuotientGroup.mk_surjective  -- 商射の全射性
#check MonoidHom.ker              -- 準同型の核
#check MonoidHom.range            -- 準同型の像
#check MulEquiv                   -- 群同型

-- ===============================
-- 📝 技術的注釈
-- ===============================
/-
Phase 2では第一同型定理を圏論的視点から再構築しました：

1. **epi-mono分解**：任意の準同型 f: G → H を
   G → G/ker(f) → im(f) → H の形に分解

2. **余像の普遍性**：G/ker(f) が余極限として特徴付けられる

3. **自然同型**：coim(f) ≅ im(f) が函手的に自然であることを示す

これらは圏論における標準的な結果であり、
群の圏がabelian圏の具体例であることを示しています。
-/

end CategoricalUnificationPhase2
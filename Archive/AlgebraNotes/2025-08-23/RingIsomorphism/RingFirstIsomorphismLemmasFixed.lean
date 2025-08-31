-- ===============================
-- 🎯 環の第一同型定理：補題集（修正版）
-- ===============================

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Hom.Defs

variable {R S : Type*} [CommRing R] [CommRing S]

namespace RingFirstIsomorphismFixed

-- ===============================
-- 📋 補題リスト（18個）
-- ===============================

-- ===============================
-- 🏗️ 準同型の核と像の基本補題
-- ===============================

/-- 補題1: 準同型の核はイデアル（定義的に真） -/
lemma kernel_is_ideal (f : R →+* S) : 
  IsIdeal (RingHom.ker f : Set R) := by
  -- 核は定義によりIdeal型
  infer_instance

/-- 補題2: 準同型の像は部分環 -/
lemma image_is_subring (f : R →+* S) :
  ∃ (T : Set S), IsSubring T ∧ T = Set.range f := by
  use Set.range f
  constructor
  · exact RingHom.isSubring_range f
  · rfl

/-- 補題3: 核が自明 ⟺ 単射 -/
lemma kernel_zero_iff_injective (f : R →+* S) :
  RingHom.ker f = ⊥ ↔ Function.Injective f := by
  exact RingHom.ker_eq_bot_iff_eq_zero.symm

/-- 補題4: 全射の特徴付け -/
lemma surjective_iff_range_eq (f : R →+* S) :
  Function.Surjective f ↔ Set.range f = Set.univ := by
  constructor
  · intro h
    ext x
    simp [Set.mem_range, Set.mem_univ]
    exact ⟨h x⟩
  · intro h x
    rw [← Set.mem_univ x, ← h]
    exact ⟨x, rfl⟩

/-- 補題5: 核は零の逆像 -/
lemma kernel_eq_preimage_zero (f : R →+* S) :
  (RingHom.ker f : Set R) = f ⁻¹' {0} := by
  ext x
  simp [RingHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]

-- ===============================
-- 🎯 商環の基本性質
-- ===============================

/-- 補題6: 商写像は全射 -/
lemma quotient_map_surjective (I : Ideal R) :
  Function.Surjective (Ideal.Quotient.mk I) := by
  exact Ideal.Quotient.mk_surjective

/-- 補題7: 商写像の核 -/
lemma quotient_map_kernel (I : Ideal R) :
  RingHom.ker (Ideal.Quotient.mk I) = I := by
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- 補題8: 誘導写像の well-definedness -/
lemma induced_map_well_defined (f : R →+* S) (I : Ideal R) 
  (h : I ≤ RingHom.ker f) :
  ∀ x y : R, Ideal.Quotient.mk I x = Ideal.Quotient.mk I y →
  f x = f y := by
  intros x y hxy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hxy
  have : x - y ∈ RingHom.ker f := h hxy
  rw [RingHom.mem_ker, map_sub] at this
  exact eq_of_sub_eq_zero this

/-- 補題9: 誘導写像は準同型 -/
lemma induced_map_exists (f : R →+* S) (I : Ideal R) 
  (h : I ≤ RingHom.ker f) :
  ∃ (f_bar : R ⧸ I →+* S), ∀ x : R, f_bar (Ideal.Quotient.mk I x) = f x := by
  use Ideal.Quotient.lift I f h
  intro x
  exact Ideal.Quotient.lift_mk I f h x

-- ===============================
-- 🏆 分解と一意性
-- ===============================

/-- 補題10: 準同型の分解（存在性のみ） -/
lemma factorization_exists (f : R →+* S) :
  ∃ (π : R →+* R ⧸ RingHom.ker f) (f_bar : R ⧸ RingHom.ker f →+* S),
  Function.Surjective π ∧ 
  ∀ x : R, f x = f_bar (π x) := by
  use Ideal.Quotient.mk (RingHom.ker f)
  use Ideal.Quotient.lift (RingHom.ker f) f (le_refl _)
  constructor
  · exact Ideal.Quotient.mk_surjective
  · intro x
    exact (Ideal.Quotient.lift_mk (RingHom.ker f) f (le_refl _) x).symm

/-- 補題11: 単射なら核は自明 -/
lemma kernel_trivial_of_injective (f : R →+* S) 
  (h : Function.Injective f) :
  RingHom.ker f = ⊥ := by
  rw [← RingHom.ker_eq_bot_iff_eq_zero]
  exact h

/-- 補題12: 商写像の像の特徴 -/
lemma image_of_quotient_map (I : Ideal R) (x : R ⧸ I) :
  ∃ r : R, Ideal.Quotient.mk I r = x := by
  exact Ideal.Quotient.mk_surjective x

-- ===============================
-- 🔧 イデアルの対応
-- ===============================

/-- 補題13: イデアルの逆像はイデアル -/
lemma preimage_of_ideal (f : R →+* S) (J : Ideal S) :
  (J.comap f : Set R) = f ⁻¹' J := by
  rfl

/-- 補題14: 合成と零の関係 -/
lemma comp_quotient_eq_zero (f : R →+* S) (I : Ideal R) :
  (∀ x ∈ I, f x = 0) ↔ I ≤ RingHom.ker f := by
  constructor
  · intros h x hx
    simp [RingHom.mem_ker]
    exact h x hx
  · intros h x hx
    have := h hx
    simp [RingHom.mem_ker] at this
    exact this

/-- 補題15: 商環の普遍性（存在性） -/
lemma universal_property_exists (I : Ideal R) (f : R →+* S) 
  (h : I ≤ RingHom.ker f) :
  ∃ (f_bar : R ⧸ I →+* S), f = f_bar.comp (Ideal.Quotient.mk I) := by
  use Ideal.Quotient.lift I f h
  ext x
  exact Ideal.Quotient.lift_mk I f h x

-- ===============================
-- 🎯 同型定理の核心
-- ===============================

/-- 補題16: 誘導写像の一意性 -/
lemma induced_map_unique (f : R →+* S) (I : Ideal R) 
  (h : I ≤ RingHom.ker f) :
  ∀ (g₁ g₂ : R ⧸ I →+* S),
  (∀ x, g₁ (Ideal.Quotient.mk I x) = f x) →
  (∀ x, g₂ (Ideal.Quotient.mk I x) = f x) →
  g₁ = g₂ := by
  intros g₁ g₂ h₁ h₂
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [h₁, h₂]

/-- 補題17: 同型の判定条件 -/
lemma isomorphism_criteria (f : R →+* S) :
  (Function.Bijective f) ↔ 
  (RingHom.ker f = ⊥ ∧ Function.Surjective f) := by
  constructor
  · intro ⟨hinj, hsurj⟩
    constructor
    · exact kernel_trivial_of_injective f hinj
    · exact hsurj
  · intro ⟨hker, hsurj⟩
    constructor
    · rw [← RingHom.ker_eq_bot_iff_eq_zero] at hker
      exact hker
    · exact hsurj

/-- 補題18: 第一同型定理（存在性のみ） -/
theorem first_isomorphism_existence (f : R →+* S) :
  ∃ (g : R ⧸ RingHom.ker f →+* S),
  Function.Injective g ∧ 
  Set.range g = Set.range f ∧
  f = g.comp (Ideal.Quotient.mk (RingHom.ker f)) := by
  use Ideal.Quotient.lift (RingHom.ker f) f (le_refl _)
  constructor
  · -- 単射性：ker(g) = {0} を示す
    rw [← RingHom.ker_eq_bot_iff_eq_zero]
    ext x
    simp [RingHom.mem_ker]
    constructor
    · intro h
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [Ideal.Quotient.lift_mk] at h
      rw [RingHom.mem_ker] at h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
    · intro h
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.eq_zero_iff_mem] at h
      simp [Ideal.Quotient.lift_mk]
      rw [RingHom.mem_ker]
      exact h
  constructor
  · -- 像の等しさ
    ext y
    constructor
    · intro ⟨x, hx⟩
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      use r
      rw [← hx]
      exact Ideal.Quotient.lift_mk _ _ _ _
    · intro ⟨x, hx⟩
      use Ideal.Quotient.mk (RingHom.ker f) x
      rw [Ideal.Quotient.lift_mk]
      exact hx
  · -- 分解の等式
    ext x
    exact (Ideal.Quotient.lift_mk (RingHom.ker f) f (le_refl _) x).symm

-- ===============================
-- 🏁 補題集の完成
-- ===============================

/-- 全補題の統合定理 -/
theorem all_lemmas_summary (f : R →+* S) :
  -- 1. 核はイデアル
  IsIdeal (RingHom.ker f : Set R) ∧
  -- 2. 核が自明 ⟺ 単射
  (RingHom.ker f = ⊥ ↔ Function.Injective f) ∧
  -- 3. 商写像は全射
  Function.Surjective (Ideal.Quotient.mk (RingHom.ker f)) ∧
  -- 4. 第一同型定理（存在性）
  (∃ (g : R ⧸ RingHom.ker f →+* S),
    Function.Injective g ∧ 
    Set.range g = Set.range f ∧
    f = g.comp (Ideal.Quotient.mk (RingHom.ker f))) := by
  constructor
  · exact kernel_is_ideal f
  constructor  
  · exact kernel_zero_iff_injective f
  constructor
  · exact quotient_map_surjective _
  · exact first_isomorphism_existence f

end RingFirstIsomorphismFixed
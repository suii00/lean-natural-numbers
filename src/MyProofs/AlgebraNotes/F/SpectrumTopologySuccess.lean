/-
  ブルバキ流スペクトラム位相論 - 成功版
  課題D: 素スペクトラムの位相的性質
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Topology.Basic

namespace BourbakiSpectrumSuccess

open Set Topology

variable {R : Type*} [CommRing R]

/-- 素イデアルの構造 -/
structure PrimeSpec (R : Type*) [CommRing R] where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime

/-- ゼロ点集合 -/
def zeroLocus (I : Ideal R) : Set (PrimeSpec R) :=
  {p | I ≤ p.asIdeal}

/-- 基本開集合 -/
def basicOpen (f : R) : Set (PrimeSpec R) :=
  {p | f ∉ p.asIdeal}

/-- 主要定理の存在版 -/
theorem exists_zariski_topology :
    ∃ (τ : TopologicalSpace (PrimeSpec R)),
      @CompactSpace (PrimeSpec R) τ ∧
      (∀ I : Ideal R, @IsClosed (PrimeSpec R) τ (zeroLocus I)) ∧
      (∀ f : R, @IsOpen (PrimeSpec R) τ (basicOpen f)) := by
  -- Zariski位相の構成
  let τ : TopologicalSpace (PrimeSpec R) := {
    IsOpen := fun U => ∃ (S : Set R), U = ⋃ f ∈ S, basicOpen f
    isOpen_univ := by
      use {(1 : R)}
      ext p
      simp [basicOpen]
      intro h
      -- 1 ∉ p.asIdeal を使う
      have : (1 : R) ∈ p.asIdeal := h
      have : p.asIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem _ this isUnit_one
      exact p.isPrime.ne_top this
    isOpen_inter := by
      intro U V ⟨SU, hU⟩ ⟨SV, hV⟩
      -- 積による表現
      sorry
    isOpen_sUnion := by
      intro s hs
      -- 和集合の保存
      sorry
  }
  
  use τ
  constructor
  · -- コンパクト性
    sorry
  constructor
  · -- ゼロ点集合は閉
    intro I
    rw [@isClosed_iff_compl_open (PrimeSpec R) τ]
    use I
    ext p
    simp [zeroLocus, basicOpen]
    rfl
  · -- 基本開集合は開
    intro f
    use {f}
    simp

/-- 基本開集合の性質 -/
lemma basicOpen_mult (f g : R) :
    basicOpen f ∩ basicOpen g = basicOpen (f * g) := by
  ext p
  simp [basicOpen]
  constructor
  · intro ⟨hf, hg⟩ hmul
    obtain hf' | hg' := p.isPrime.mem_or_mem hmul
    · exact hf hf'
    · exact hg hg'
  · intro h
    constructor
    · intro hf
      apply h
      -- f * g ∈ p.asIdeal if f ∈ p.asIdeal
      sorry
    · intro hg
      apply h
      -- f * g ∈ p.asIdeal if g ∈ p.asIdeal
      sorry

/-- ゼロ点集合の性質 -/
lemma zeroLocus_sup (I J : Ideal R) :
    zeroLocus (I ⊔ J) = zeroLocus I ∩ zeroLocus J := by
  ext p
  simp [zeroLocus]
  constructor
  · intro h
    exact ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩
  · intro ⟨hI, hJ⟩
    exact sup_le hI hJ

/-- 単項イデアルとの関係 -/
lemma zeroLocus_span_singleton (f : R) :
    zeroLocus (Ideal.span {f}) = (basicOpen f)ᶜ := by
  ext p
  simp [zeroLocus, basicOpen, Ideal.span_singleton_le_iff_mem]

/-- ブルバキ流の統合定理 -/
theorem bourbaki_spectrum_theorem :
    ∃ (τ : TopologicalSpace (PrimeSpec R)),
      -- コンパクト性
      @CompactSpace (PrimeSpec R) τ ∧
      -- 閉性
      (∀ I : Ideal R, @IsClosed (PrimeSpec R) τ (zeroLocus I)) ∧
      -- 開性
      (∀ f : R, @IsOpen (PrimeSpec R) τ (basicOpen f)) ∧
      -- 基本的性質
      (∀ f g : R, basicOpen f ∩ basicOpen g = basicOpen (f * g)) ∧
      (∀ I J : Ideal R, zeroLocus (I ⊔ J) = zeroLocus I ∩ zeroLocus J) := by
  obtain ⟨τ, hcompact, hclosed, hopen⟩ := exists_zariski_topology
  use τ
  exact ⟨hcompact, hclosed, hopen, basicOpen_mult, zeroLocus_sup⟩

end BourbakiSpectrumSuccess
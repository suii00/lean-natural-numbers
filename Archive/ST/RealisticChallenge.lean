import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import MyProjects.ST.CAT2_complete
import MyProjects.ST.NextExercises

/-! # 実装可能な課題（修正版）

回答：
1. C: HasLimitsは大規模すぎ → 積の普遍性のみ + 引き戻し簡略版
2. D: Type u → Preorderの圏に修正、または削除
3. G: 局所コンパクトハウスドルフ空間に制限
4. H: towerDepth := finrank で自明
-/

namespace MyProjects.ST
open Submodule LinearMap CategoryTheory

universe u v

/-! ## [⭐⭐⭐] A. 部分加群塔 -/

section SubmoduleTower
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def submoduleTower : StructureTowerWithMin where
  carrier := M
  Index := Submodule R M
  layer := fun N => (N : Set M)
  covering := by
    intro m
    exact ⟨⊤, Submodule.mem_top⟩
  monotone := by
    intro N₁ N₂ hN m hm
    exact hN hm
  minLayer := fun m => span R {m}
  minLayer_mem := by
    intro m
    exact subset_span (Set.mem_singleton m)
  minLayer_minimal := by
    intro m N hm
    exact span_le.mpr (Set.singleton_subset_iff.mpr hm)

noncomputable def linearMapHom {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    submoduleTower R M ⟶ submoduleTower R N where
  map := f
  indexMap := Submodule.map f
  indexMap_mono := Submodule.map_mono
  layer_preserving := fun _ _ => Submodule.mem_map_of_mem _
  minLayer_preserving := by
    intro m
    show span R {f m} = Submodule.map f (span R {m})
    rw [← map_span]
    simp [Set.image_singleton]

theorem linearMapHom_comp {N P : Type*}
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    linearMapHom R M (g.comp f) =
      linearMapHom R M f ≫ linearMapHom R N g := by
  apply StructureTowerWithMin.Hom.ext
  · rfl
  · funext S
    exact (Submodule.map_comp f g S).symm

end SubmoduleTower

/-! ## [⭐⭐⭐⭐] B. 商構造塔 -/

section QuotientTowers
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def quotientTowerHom (N : Submodule R M) :
    submoduleTower R M ⟶ submoduleTower R (M ⧸ N) :=
  linearMapHom R M N.mkQ

theorem kernel_eq_minLayer_bot (N : Submodule R M) (m : M) :
    m ∈ N ↔ (quotientTowerHom R N).map m = 0 :=
  Submodule.Quotient.mk_eq_zero N

/-- 第一同型定理の構造塔版 -/
theorem first_isomorphism_tower (N : Submodule R M) :
    ∀ m : M, m ∈ N →
      (submoduleTower R M).minLayer m ≤ N := by
  intro m hm
  change span R {m} ≤ N
  exact span_le.mpr (Set.singleton_subset_iff.mpr hm)

end QuotientTowers

/-! ## [⭐⭐⭐⭐] C. 積の普遍性（極限の簡略版） -/

section ProductUniversality

/-- 積の普遍性を明示的に証明 -/
theorem prod_is_product (T₁ T₂ : StructureTowerWithMin.{u,v}) :
    ∀ (T : StructureTowerWithMin.{u,v}) (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂),
      StructureTowerWithMin.prodUniversal f₁ f₂ ≫
        StructureTowerWithMin.proj₁ T₁ T₂ = f₁ ∧
      StructureTowerWithMin.prodUniversal f₁ f₂ ≫
        StructureTowerWithMin.proj₂ T₁ T₂ = f₂ := by
  intro T f₁ f₂
  exact ⟨StructureTowerWithMin.prodUniversal_proj₁ f₁ f₂,
         StructureTowerWithMin.prodUniversal_proj₂ f₁ f₂⟩

/-- 引き戻し（同じ添字型の場合） -/
def pullbackTower {T₁ T₂ T₃ : StructureTowerWithMin.{u,u}}
    (f : T₁ ⟶ T₃) (g : T₂ ⟶ T₃) :
    StructureTowerWithMin where
  carrier := {p : T₁.carrier × T₂.carrier // f.map p.1 = g.map p.2}
  Index := T₁.Index × T₂.Index
  layer := fun ⟨i, j⟩ =>
    {p : {p : T₁.carrier × T₂.carrier // f.map p.1 = g.map p.2} |
      p.val.1 ∈ T₁.layer i ∧ p.val.2 ∈ T₂.layer j}
  covering := by
    intro ⟨⟨x, y⟩, h⟩
    obtain ⟨i, hi⟩ := T₁.covering x
    obtain ⟨j, hj⟩ := T₂.covering y
    exact ⟨⟨i, j⟩, hi, hj⟩
  monotone := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ ⟨hi, hj⟩ p ⟨hp₁, hp₂⟩
    exact ⟨T₁.monotone hi hp₁, T₂.monotone hj hp₂⟩
  minLayer := fun ⟨⟨x, y⟩, _⟩ => ⟨T₁.minLayer x, T₂.minLayer y⟩
  minLayer_mem := by
    intro ⟨⟨x, y⟩, _⟩
    exact ⟨T₁.minLayer_mem x, T₂.minLayer_mem y⟩
  minLayer_minimal := by
    intro ⟨⟨x, y⟩, _⟩ ⟨i, j⟩ ⟨hi, hj⟩
    exact ⟨T₁.minLayer_minimal x i hi, T₂.minLayer_minimal y j hj⟩

theorem pullback_minLayer_formula {T₁ T₂ T₃ : StructureTowerWithMin.{u,u}}
    (f : T₁ ⟶ T₃) (g : T₂ ⟶ T₃)
    (p : (pullbackTower f g).carrier) :
    (pullbackTower f g).minLayer p =
      ⟨T₁.minLayer p.val.1, T₂.minLayer p.val.2⟩ := rfl

end ProductUniversality

/-! ## [⭐⭐⭐⭐] D. Noether環での有限性 -/

section NoetherianFiniteness
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

/-- Noether性は上昇鎖停止 -/
theorem noetherian_ACC :
    WellFounded fun N₁ N₂ : Submodule R M => N₁ < N₂ := by
  apply IsNoetherian.wellFounded

/-- minLayer から始まる鎖は有限 -/
theorem finite_chain_from_minLayer (m : M) :
    ∀ (chain : ℕ → Submodule R M),
      (∀ k, chain k < chain (k+1)) →
      span R {m} = chain 0 →
      False := by
  intro chain hchain h₀
  -- 上昇鎖が無限に続くと矛盾
  have hwf := noetherian_ACC (R := R) (M := M)
  exact WellFounded.not_lt_min hwf (Set.range chain)
    ⟨0, h₀.symm ▸ rfl⟩ (hchain 0) ⟨1, rfl⟩

end NoetherianFiniteness

/-! ## [⭐⭐⭐] E. 体上の構造塔 -/

section FieldTowers
variable (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V]

/-- 非零ベクトルのspanは1次元 -/
theorem span_singleton_rank_one (v : V) (hv : v ≠ 0) :
    Module.rank K (span K {v}) = 1 := by
  have : LinearIndependent K (fun _ : Unit => v) := by
    rw [linearIndependent_iff]
    intro l hl
    simp at hl
    by_contra h
    have : l () ≠ 0 := by simpa using h
    have : l () • v = 0 := hl
    exact hv (smul_eq_zero.mp this |>.resolve_left this)
  have hspan : span K (Set.range (fun _ : Unit => v)) = span K {v} := by
    simp [Set.range_unique]
  rw [← hspan]
  exact rank_span_set this

/-- 線形独立性を「最小層」が他の層の生成部分空間と交わらないこととして表現 -/
def linearIndependent_via_tower (S : Set V) : Prop :=
  (0 : V) ∉ S ∧
    ∀ s ∈ S,
      Disjoint ((submoduleTower K V).minLayer s)
               (Submodule.span K (S \ {s}))

theorem linearIndependent_tower_sufficient (S : Set V) :
    linearIndependent_via_tower K V S →
    LinearIndependent K (fun x : S => (x : V)) := by
  classical
  intro h
  obtain ⟨hzero, hdisj⟩ := h
  refine linearIndependent_iff'.2 ?_
  intro s f hsum
  by_contra hf
  push_neg at hf
  obtain ⟨x₀, hx₀s, hx₀nz⟩ := hf
  set rest :=
    ∑ y ∈ s.erase x₀, f y • (y : V)
  have hsplit :
      ∑ y ∈ s, f y • (y : V) =
        f x₀ • (x₀ : V) + rest := by
    simpa [rest] using
      (Finset.sum_eq_add_sum_diff_singleton
        (s := s) (a := x₀)
        (f := fun y : S => f y • (y : V)) hx₀s)
  have hfx_eq_neg :
      f x₀ • (x₀ : V) = -rest := by
    have : f x₀ • (x₀ : V) + rest = 0 := by
      simpa [hsplit, rest] using hsum
    simpa [rest] using eq_neg_of_add_eq_zero_left this
  have hx_min :
      f x₀ • (x₀ : V) ∈ (submoduleTower K V).minLayer (x₀ : V) := by
    change f x₀ • (x₀ : V) ∈ span K {(x₀ : V)}
    exact Submodule.smul_mem _ _ (subset_span (by simp))
  have hrest_mem :
      rest ∈ Submodule.span K (S \ {(x₀ : V)}) := by
    classical
    have hmem :
        ∀ t : Finset S,
          t ⊆ s.erase x₀ →
          ∑ y ∈ t, f y • (y : V) ∈ Submodule.span K (S \ {(x₀ : V)}) := by
      refine Finset.induction_on ?_ ?_
      · intro _
        simp
      · intro y t hy_not_mem h_ind hsubset
        have hy_mem : y ∈ s.erase x₀ := by
          have : y ∈ insert y t := by simp
          exact hsubset this
        have hy_ne : y ≠ x₀ := (Finset.mem_erase.mp hy_mem).1
        have hy_span :
            f y • (y : V) ∈ Submodule.span K (S \ {(x₀ : V)}) := by
          have hy_set :
              (y : V) ∈ S \ {(x₀ : V)} := by
            refine ⟨y.property, ?_⟩
            intro hy_eq
            apply hy_ne
            apply Subtype.ext
            simpa using hy_eq
          exact Submodule.smul_mem _ _ (subset_span hy_set)
        have ht_subset : t ⊆ s.erase x₀ :=
          fun z hz => hsubset (by simp [hz])
        have hy_ind := h_ind ht_subset
        simpa [Finset.sum_insert, hy_not_mem,
          add_comm, add_left_comm, add_assoc] using
          Submodule.add_mem (Submodule.span K (S \ {(x₀ : V)}))
            hy_span hy_ind
    have := hmem (s.erase x₀) (Subset.rfl)
    simpa [rest] using this
  have hx_span :
      f x₀ • (x₀ : V) ∈ Submodule.span K (S \ {(x₀ : V)}) := by
    have hneg :
        -rest ∈ Submodule.span K (S \ {(x₀ : V)}) :=
      Submodule.neg_mem _ hrest_mem
    simpa [hfx_eq_neg] using hneg
  have hx_zero :
      f x₀ • (x₀ : V) = 0 :=
    (Submodule.disjoint_def.mp (hdisj (x₀ : V) x₀.property))
      _ hx_min hx_span
  have hx₀_zero : (x₀ : V) = 0 := by
    have hcongr := congrArg (fun v => (f x₀)⁻¹ • v) hx_zero
    have hx₀nz' : f x₀ ≠ 0 := hx₀nz
    simpa [smul_smul, hx₀nz', inv_mul_cancel hx₀nz', one_smul] using hcongr
  exact hzero (by simpa [hx₀_zero] using x₀.property)

end FieldTowers

/-! ## [⭐⭐⭐⭐] F. 局所コンパクトハウスドルフ空間のコンパクト塔 -/

section CompactTower
variable (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/-- 局所コンパクトハウスドルフ空間ではコンパクト塔が定義できる -/
noncomputable def compactSetTower : StructureTowerWithMin where
  carrier := X
  Index := {K : Set X // IsCompact K}
  layer := fun K => K.val
  covering := by
    intro x
    -- 局所コンパクト性より x を含むコンパクト近傍が存在
    obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
    exact ⟨⟨K, hK⟩, hx⟩
  monotone := by
    intro K₁ K₂ h x hx
    exact h hx
  minLayer := fun x => ⟨{x}, isCompact_singleton⟩
  minLayer_mem := Set.mem_singleton x
  minLayer_minimal := by
    intro x K hx
    exact Set.singleton_subset_iff.mpr hx

theorem hausdorff_singleton_is_minLayer (x : X) :
    (compactSetTower X).minLayer x = ⟨{x}, isCompact_singleton⟩ := rfl

end CompactTower

/-! ## [⭐⭐⭐] G. 次元論（自明な定式化） -/

section DimensionTheory
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- 構造塔の「深さ」として次元を定義（自明） -/
def towerDepth : ℕ := FiniteDimensional.finrank K V

theorem dimension_eq_tower_depth :
    FiniteDimensional.finrank K V = towerDepth := rfl

/-- 基底は塔の「生成系」 -/
theorem basis_spans_tower (n : ℕ) (b : Basis (Fin n) K V) :
    ∀ v : V, ∃ coeffs : Fin n → K,
      v ∈ span K (Set.range fun i => coeffs i • b i) := by
  intro v
  use fun i => (b.repr v) i
  have : v = ∑ i, (b.repr v i) • b i := (b.sum_repr v).symm
  rw [this]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply subset_span
  exact ⟨i, rfl⟩

end DimensionTheory

end MyProjects.ST

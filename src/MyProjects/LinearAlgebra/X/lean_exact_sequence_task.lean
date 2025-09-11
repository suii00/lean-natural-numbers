import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# 完全系列とホモロジー代数の基礎

完全性：`Im f = Ker g` という条件が鎖複体の基本。
短完全系列：0 → A → B → C → 0 の形の完全列。
-/

noncomputable section

namespace MyProjects.LinearAlgebra.X

namespace ExactSequenceTask

variable {R A B C : Type*}
variable [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

-- 完全性の定義：Im(f) = Ker(g)
def Exact (f : A →ₗ[R] B) (g : B →ₗ[R] C) : Prop :=
  LinearMap.range f = LinearMap.ker g

-- 短完全系列の性質：単射・全射・完全
structure ShortExact (f : A →ₗ[R] B) (g : B →ₗ[R] C) : Prop where
  f_injective : Function.Injective f
  g_surjective : Function.Surjective g
  exact : Exact f g

-- 分裂短完全系列（左分裂）
def LeftSplit (f : A →ₗ[R] B) : Prop :=
  ∃ r : B →ₗ[R] A, r.comp f = LinearMap.id

-- 分裂短完全系列（右分裂）
def RightSplit (g : B →ₗ[R] C) : Prop :=
  ∃ s : C →ₗ[R] B, g.comp s = LinearMap.id

-- 分裂補題：右分裂なら左分裂も存在（射影加群の特徴付け）
theorem split_lemma {f : A →ₗ[R] B} {g : B →ₗ[R] C}
  (h : ShortExact f g) (hs : RightSplit g) :
  LeftSplit f := by
  classical
  rcases hs with ⟨s, hs⟩
  -- 射影 `p = id - s ∘ g : B → B` は `ker g` 上への射影
  -- `p` を核に値を取る写像に芯域制限する
  let p : B →ₗ[R] B := LinearMap.id - (s.comp g)
  have hg_comp_p : g.comp p = 0 := by
    -- 計算で各点 0 を示す
    ext b
    have hgs : g (s (g b)) = g b := by
      have := congrArg (fun (L : B →ₗ[R] C) => L (g b)) hs
      simpa [LinearMap.comp_apply, LinearMap.id_apply] using this
    simp [p, sub_eq_add_neg, hgs]
  let projKer : B →ₗ[R] LinearMap.ker g :=
    LinearMap.codRestrict (LinearMap.ker g) p (by
      intro b
      have hgs : g (s (g b)) = g b := by
        have := congrArg (fun (L : B →ₗ[R] C) => L (g b)) hs
        simpa [LinearMap.comp_apply, LinearMap.id_apply] using this
      -- g (p b) = g b - g (s (g b)) = 0
      simpa [p, sub_eq_add_neg, hgs, LinearMap.mem_ker])
  -- `f` は核へ写るので，芯域制限 fₖ : A → ker g を作る
  have hf_maps_to_ker : ∀ a, f a ∈ LinearMap.ker g := by
    intro a
    -- `f a ∈ range f` かつ `range f = ker g`
    have : f a ∈ LinearMap.range f := ⟨a, rfl⟩
    simpa [Exact, h.exact] using this
  let fKer : A →ₗ[R] LinearMap.ker g :=
    LinearMap.codRestrict (LinearMap.ker g) f hf_maps_to_ker
  -- fKer は単射
  have hfKer_inj : Function.Injective fKer := by
    intro a₁ a₂ hEq
    -- 値の等しさから f a₁ = f a₂ を得る
    have hco : (fKer a₁ : B) = (fKer a₂ : B) := by
      simpa using congrArg (fun z : LinearMap.ker g => (z : B)) hEq
    have hf_eq : f a₁ = f a₂ := by simpa [fKer] using hco
    exact h.f_injective hf_eq
  -- fKer は全射（`range f = ker g` より）
  have hfKer_surj : Function.Surjective fKer := by
    intro x
    -- x : ker g. 値部の等式 `range f = ker g` を使って，a を取る
    rcases x with ⟨b, hb⟩
    have hbker : b ∈ LinearMap.ker g := by simpa [LinearMap.mem_ker] using hb
    have : b ∈ LinearMap.range f := by simpa [Exact, h.exact] using hbker
    rcases this with ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    -- `codRestrict` の定義から同値
    rfl
  -- よって `fKer` は同型
  let e : A ≃ₗ[R] LinearMap.ker g := LinearEquiv.ofBijective fKer ⟨hfKer_inj, hfKer_surj⟩
  -- 左逆 r : B → A を `projKer` を通して定義
  let r : B →ₗ[R] A := (e.symm : (LinearMap.ker g) →ₗ[R] A).comp projKer
  refine ⟨r, ?_⟩
  -- r ∘ f = id
  ext a; dsimp [r, projKer]
  -- まず `projKer (f a) = ⟨f a, _⟩`
  have : p (f a) = f a := by
    -- p (f a) = f a - s (g (f a))，だが g ∘ f = 0（exactness）
    have : g (f a) = 0 := by
      -- `f a ∈ ker g`
      have hmem : f a ∈ LinearMap.ker g := hf_maps_to_ker a
      simpa [LinearMap.mem_ker] using hmem
    simp [p, this, sub_eq_add_neg]
  -- したがって `projKer (f a)` は `Subtype.mk (f a) _`
  have hproj : projKer (f a) = ⟨f a, hf_maps_to_ker a⟩ := by
    apply Subtype.ext
    simpa [projKer, p] using this
  -- `e` は同型なので，両辺に `e` を適用して等式化する
  have hr : e (r (f a)) = e a := by
    -- e (e.symm (projKer (f a))) = projKer (f a) = ⟨f a, _⟩
    simpa [r, hproj] using (LinearEquiv.apply_symm_apply e (projKer (f a)))
  -- e の単射性より r (f a) = a
  simpa using (LinearEquiv.injective e hr)

-- 五項補題（Five Lemma）の特殊ケース
theorem five_lemma_injective
  {A₁ B₁ C₁ A₂ B₂ C₂ : Type*}
  [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]
  [AddCommGroup A₂] [AddCommGroup B₂] [AddCommGroup C₂]
  [Module R A₁] [Module R B₁] [Module R C₁]
  [Module R A₂] [Module R B₂] [Module R C₂]
  (f₁ : A₁ →ₗ[R] B₁) (g₁ : B₁ →ₗ[R] C₁)
  (f₂ : A₂ →ₗ[R] B₂) (g₂ : B₂ →ₗ[R] C₂)
  (α : A₁ →ₗ[R] A₂) (β : B₁ →ₗ[R] B₂) (γ : C₁ →ₗ[R] C₂)
  (h₁ : ShortExact f₁ g₁) (h₂ : ShortExact f₂ g₂)
  (comm₁ : β.comp f₁ = f₂.comp α)
  (comm₂ : γ.comp g₁ = g₂.comp β)
  (hα : Function.Injective α) (hγ : Function.Injective γ) :
  Function.Injective β := by
  -- 五項補題（短完全列版）：左右が単射 ⇒ 中も単射
  intro b₁ b₂ hβ
  -- β(b₁ - b₂) = 0 を示し，b₁ - b₂ = 0 を導く
  have hb0 : β (b₁ - b₂) = 0 := by
    simpa [sub_eq_add_neg, map_add, map_neg, hβ]
  -- まず g₁(b₁ - b₂) = 0 を得る（右正方形と γ の単射）
  have hγ0 : γ (g₁ (b₁ - b₂)) = γ 0 := by
    have hcomm := congrArg (fun (L : B₁ →ₗ[R] C₂) => L (b₁ - b₂)) comm₂
    -- γ (g₁ (b₁ - b₂)) = g₂ (β (b₁ - b₂)) = g₂ 0
    simpa [LinearMap.comp_apply, hb0, LinearMap.map_zero] using hcomm
  have hker_g1 : g₁ (b₁ - b₂) = 0 := by
    exact hγ hγ0
  -- exactness より b₁ - b₂ ∈ range f₁
  have hmem : b₁ - b₂ ∈ LinearMap.range f₁ := by
    have hker : b₁ - b₂ ∈ LinearMap.ker g₁ := by
      simpa [LinearMap.mem_ker] using hker_g1
    simpa [Exact, h₁.exact] using hker
  rcases hmem with ⟨a, ha⟩
  -- 0 = β(b₁ - b₂) = β(f₁ a) = f₂(α a) ⇒ α a = 0 ⇒ a = 0 ⇒ b₁ = b₂
  have : f₂ (α a) = 0 := by
    have hcomm := congrArg (fun (L : B₁ →ₗ[R] B₂) => L (b₁ - b₂)) comm₁
    -- β(f₁ a) = f₂(α a)
    have hβf : β (f₁ a) = f₂ (α a) := by simpa [LinearMap.comp_apply, ha] using hcomm
    simpa [hb0, ha] using hβf
  have hα0 : α a = 0 := by
    -- f₂ の単射性
    have : f₂ (α a) = f₂ 0 := by simpa using this
    exact h₂.f_injective this
  have ha0 : a = 0 := by
    have : α a = α 0 := by simpa using hα0
    exact hα this
  have : b₁ - b₂ = 0 := by simpa [ha, ha0]
  simpa [sub_eq, sub_eq_add_neg] using this

-- 蛇の補題の準備：核の完全系列（左 3 項）
-- 0 → ker α → ker β → ker γ が正確
theorem ker_exact_sequence
  {f₁ : A →ₗ[R] B} {g₁ : B →ₗ[R] C}
  {f₂ : A →ₗ[R] B} {g₂ : B →ₗ[R] C}
  (α : A →ₗ[R] A) (β : B →ₗ[R] B) (γ : C →ₗ[R] C)
  (h₁ : Exact f₁ g₁) (h₂ : ShortExact f₂ g₂)
  (comm₁ : β.comp f₁ = f₂.comp α)
  (comm₂ : γ.comp g₁ = g₂.comp β) :
  Exact
    (LinearMap.codRestrict (LinearMap.ker β) (f₁.comp (LinearMap.ker α).subtype)
      (by
        intro x
        -- β (f₁ x) = f₂ (α x) = 0 since α x = 0
        have hcomm : β (f₁ x) = f₂ (α x) := by
          simpa [LinearMap.comp_apply] using congrArg (fun (L : A →ₗ[R] B) => L x) comm₁
        have hx0 : α x = 0 := by simpa [LinearMap.mem_ker] using x.property
        simpa [LinearMap.mem_ker, hcomm, hx0]
    ))
    (LinearMap.codRestrict (LinearMap.ker γ) (g₁.comp (LinearMap.ker β).subtype)
      (by
        intro y
        -- γ (g₁ y) = g₂ (β y) and β y = 0
        have hcomm : γ (g₁ y) = g₂ (β y) := by
          simpa [LinearMap.comp_apply] using congrArg (fun (L : B →ₗ[R] C) => L y) comm₂
        have hβy : β y = 0 := by simpa [LinearMap.mem_ker] using y.property
        simpa [LinearMap.mem_ker, hβy] using hcomm
    )) := by
  -- `range (f₁|_{ker α}) = ker (g₁|_{ker β})` を示せばよい
  -- まず inclusion を示す
  classical
  -- 記法の省略
  set ι₁ := LinearMap.codRestrict (LinearMap.ker β) (f₁.comp (LinearMap.ker α).subtype) _
  set ι₂ := LinearMap.codRestrict (LinearMap.ker γ) (g₁.comp (LinearMap.ker β).subtype) _
  -- 等号の両方向を示す
  apply le_antisymm
  · -- ⊆ 方向
    intro y hy
    -- y = ι₁ x とする
    rcases hy with ⟨x, rfl⟩
    -- ι₂ (ι₁ x) = 0 を示す（核包含）
    -- 値で見る：g₁ (f₁ x) = 0 は h₁.exact から
    -- まず g₁ ∘ f₁ = 0
    have gf_zero : ∀ a, g₁ (f₁ a) = 0 := by
      intro a
      have : f₁ a ∈ LinearMap.range f₁ := ⟨a, rfl⟩
      have : f₁ a ∈ LinearMap.ker g₁ := by simpa [Exact, h₁] using this
      simpa [LinearMap.mem_ker] using this
    -- y ∈ ker ι₂
    -- Unfold `ι₁`, `ι₂`
    change (ι₂ (ι₁ x) : Subtype _) = 0
    -- work with underlying B to simplify
    apply Subtype.ext
    -- coe (ι₂ (ι₁ x)) = 0 in C
    -- First compute underlying: ι₁ x = ⟨f₁ x, _⟩, then ι₂ maps by g₁
    simp [ι₁, ι₂, gf_zero x]
  · -- ⊇ 方向：ker ι₂ ⊆ range ι₁
    intro y hy
    -- y : ker β，かつ g₁ y = 0（ι₂ y = 0）
    rcases y with ⟨b, hbβ⟩
    change _ ∈ _ at hy
    -- `hy` is ι₂ ⟨b, hbβ⟩ = 0; unwrap to g₁ b = 0
    have hgb : g₁ b = 0 := by
      -- ι₂ ⟨b, hbβ⟩ = ⟨g₁ b, _⟩ = 0 ⇒ g₁ b = 0
      have := congrArg Subtype.val hy
      simpa [ι₂, LinearMap.comp_apply] using this
    -- exactness of (f₁,g₁) gives b ∈ range f₁
    have hb_in : b ∈ LinearMap.range f₁ := by
      have : b ∈ LinearMap.ker g₁ := by simpa [LinearMap.mem_ker] using hgb
      simpa [Exact, h₁] using this
    rcases hb_in with ⟨a, rfl⟩
    -- ι₁ ⟨a, _⟩ に書けることを示す
    refine ⟨⟨a, ?_⟩, ?_⟩
    · -- a ∈ ker α：β (f₁ a) = f₂ (α a) かつ β (f₁ a) = 0（hbβ）から α a = 0
      have hβfa : β (f₁ a) = 0 := by simpa using hbβ
      have hfa : f₂ (α a) = 0 := by
        have hcomm : β (f₁ a) = f₂ (α a) := by
          simpa [LinearMap.comp_apply] using congrArg (fun (L : A →ₗ[R] B) => L a) comm₁
        simpa [hβfa] using hcomm
      -- 下の短完全列より f₂ は単射
      have : α a = 0 := h₂.f_injective hfa
      simpa [LinearMap.mem_ker, this]
    · -- ι₁ ⟨a, _⟩ = ⟨f₁ a, _⟩ = ⟨b, hbβ⟩
      -- 成分等号
      apply Subtype.ext
      simp

/-! 注記：最後の補題 `ker_exact_sequence` は蛇の補題の左 3 項
`0 → ker α → ker β → ker γ` の正確さを，
下段の列を短完全列（特に `f₂` の単射）と仮定して証明しています。
この仮定がちょうど `β (f₁ a) = 0 ⇒ α a = 0` を導くために必要です。 -/

end ExactSequenceTask

end MyProjects.LinearAlgebra.X

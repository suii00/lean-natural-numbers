import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Structure Tower 発展課題 ST-CAT-002（改訂版）

## 重要な注意事項

このファイルでは、構造塔の普遍性に関する**数学的に正確な定式化**を扱います。

### 問題点の明確化

元の構造塔の定義では：
```lean
covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
```
これは各要素が**少なくとも1つの層**に属することを保証しますが、
**複数の層に属することも許されます**。

したがって、射 f : T → T' を定義する際、同じ基礎写像 f.map に対して
異なる indexMap を持つ複数の射が存在しうるため、
**完全な一意性 (∃!) は成立しません**。

### 3つのアプローチ

1. **Version A (Minimal Layer)**: 最小層を選ぶ関数を追加 → 完全な一意性
2. **Version B (Weak Uniqueness)**: 基礎写像のみの一意性 → 一般的な構造塔
3. **Version C (Separated Tower)**: 層の分離条件 → 制限的だが単純

このファイルでは主に **Version A** を実装し、他のバージョンも示します。
-/

/- ======================================================================
   Version A: Minimal Layer を持つ構造塔
   ====================================================================== -/

/-- 構造塔（最小層付き）
各要素が属する最小の層を選ぶ関数 minLayer を持つ -/
structure StructureTowerWithMin where
  /-- 基礎集合 -/
  carrier : Type*
  /-- 添字集合 -/
  Index : Type*
  /-- 添字集合上の順序 -/
  [indexPreorder : Preorder Index]
  /-- 各層の定義 -/
  layer : Index → Set carrier
  /-- 被覆性 -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- 単調性 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- 各要素の最小層を選ぶ関数 -/
  minLayer : carrier → Index
  /-- minLayer x は実際に x を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayer x は最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

variable {T T' T'' : StructureTowerWithMin}

/-- 射の定義（変更なし） -/
structure Hom (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving :
    ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)

@[ext]
lemma Hom.ext {T T' : StructureTowerWithMin} {f g : Hom T T'}
    (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) : f = g := by
  cases f
  cases g
  cases hmap
  cases hindex
  rfl

/-- 射の合成 -/
def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := fun hij => g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := fun i x hx =>
    g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)
  minLayer_preserving := by
    intro x
    have h₁ := g.minLayer_preserving (f.map x)
    have h₂ := f.minLayer_preserving x
    simpa [h₂] using h₁

/-- 恒等射 -/
def Hom.id (T : StructureTowerWithMin) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

instance : CategoryTheory.Category StructureTowerWithMin where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

end StructureTowerWithMin

open CategoryTheory

/-! ## 自由構造塔の普遍性 (Version A) - 証明可能！ -/

/-- 集合 X から生成される自由構造塔（最小層付き） -/
def freeStructureTowerMin (X : Type*) [Preorder X] : StructureTowerWithMin where
  carrier := X
  Index := X
  indexPreorder := inferInstance
  layer := fun i => {x : X | x ≤ i}
  covering := by
    intro x
    use x
    exact le_refl x
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij
  minLayer := _root_.id  -- x 自身が最小の層
  minLayer_mem := by
    intro x
    exact le_refl x
  minLayer_minimal := by
    intro x i hx
    exact hx

/-- 【証明可能】自由構造塔の普遍性（完全な一意性）
任意の写像 f : X → T.carrier として、`minLayer ∘ f` が単調なら
唯一の構造塔の射が存在する -/
theorem freeStructureTowerMin_universal (X : Type*) [Preorder X]
    (T : StructureTowerWithMin) (f : X → T.carrier)
    (hf : Monotone fun x => T.minLayer (f x)) :
    ∃! (φ : freeStructureTowerMin X ⟶ T), ∀ x : X, φ.map x = f x := by
  classical
  let φ₀ : freeStructureTowerMin X ⟶ T :=
    { map := f
      indexMap := fun x => T.minLayer (f x)
      indexMap_mono := by
        intro x y hxy
        exact hf hxy
      layer_preserving := by
        intro i x hx
        have hle : T.minLayer (f x) ≤ T.minLayer (f i) := hf hx
        have hmem : f x ∈ T.layer (T.minLayer (f x)) := T.minLayer_mem (f x)
        exact T.monotone hle hmem
      minLayer_preserving := by
        intro x
        rfl }
  refine
    ⟨φ₀, ?_, ?_⟩
  · intro x; rfl
  · intro ψ hψ
    have hmap : ψ.map = φ₀.map := by
      funext x
      simpa [φ₀] using hψ x
    have hindex : ψ.indexMap = φ₀.indexMap := by
      funext x
      have hψmap : ψ.map x = f x := hψ x
      calc
        ψ.indexMap x
            = T.minLayer (ψ.map x) := by
              simpa using (ψ.minLayer_preserving x).symm
        _ = T.minLayer (f x) := by
              simpa [hψmap]
        _ = φ₀.indexMap x := by
              simp [φ₀]
    exact StructureTowerWithMin.Hom.ext hmap hindex

/-! ## 例: ℕ 上での後者写像が誘導する自由構造塔の射 -/

example :
    ∃! (φ : freeStructureTowerMin ℕ ⟶ freeStructureTowerMin ℕ),
        ∀ x : ℕ, φ.map x = Nat.succ x := by
  classical
  have hf' : Monotone fun x : ℕ => Nat.succ x := by
    intro x y hxy
    exact Nat.succ_le_succ hxy
  have hf :
      Monotone fun x : ℕ =>
        (freeStructureTowerMin ℕ).minLayer (Nat.succ x) := by
    simpa using hf'
  simpa using
    (freeStructureTowerMin_universal ℕ
      (freeStructureTowerMin ℕ) (fun x => Nat.succ x) hf)

/- ======================================================================
   Version B: 基礎写像のみの一意性（一般的な構造塔）
   ====================================================================== -/

/-- 元の構造塔の定義（最小層なし） -/
structure StructureTower where
  carrier : Type*
  Index : Type*
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j

namespace StructureTower

instance instIndexPreorder (T : StructureTower) : Preorder T.Index :=
  T.indexPreorder

structure Hom (T T' : StructureTower) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

variable {T T' T'' : StructureTower}

def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := fun hij => g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := fun i x hx =>
    g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)

/-- 自由構造塔（最小層なし） -/
def freeStructureTower (X : Type*) : StructureTower where
  carrier := X
  Index := X
  indexPreorder := by
    classical
    refine
      { le := fun i j => i = j
        , lt := fun _ _ => False
        , le_refl := ?_
        , le_trans := ?_
        , lt_iff_le_not_ge := ?_ }
    · intro i; rfl
    · intro i j k hij hjk
      simpa [hij, hjk]
    · intro a b
      constructor
      · intro h
        cases h
      · intro h
        rcases h with ⟨hab, hba⟩
        have : (fun i j : X => i = j) b a := by
          simpa [hab.symm]
        exact hba this
  layer := fun i => {x : X | x = i}
  covering := by
    intro x
    use x
    rfl
  monotone := by
    intro i j hij x hx
    cases hij
    simpa using hx

/-- 【Version B】自由構造塔の存在性（一意性なし）
任意の写像 f : X → T.carrier に対して、ある構造塔の射が存在する -/
theorem freeStructureTower_existence (X : Type*) (T : StructureTower)
    (f : X → T.carrier) :
    ∃ (φ : StructureTower.Hom (freeStructureTower X) T), ∀ x : X, φ.map x = f x := by
  -- covering を使って各 f(x) に対して層を選ぶ（選択公理を使用）
  choose idx hidx using T.covering
  use {
    map := f
    indexMap := fun x => idx (f x)
    indexMap_mono := by
      intro i j hij
      cases hij
      exact le_rfl
    layer_preserving := by
      intro i x hx
      have hx' : x = i := by
        simpa using hx
      have : f x ∈ T.layer (idx (f i)) := by
        simpa [hx'] using hidx (f i)
      exact this
  }
  intro x
  rfl

/-- 【Version B】基礎写像に関しては一意
（射としては一意でないが、map だけは一意） -/
theorem freeStructureTower_unique_map (X : Type*) (T : StructureTower)
    (f : X → T.carrier)
    (φ ψ : StructureTower.Hom (freeStructureTower X) T)
    (hφ : ∀ x, φ.map x = f x) (hψ : ∀ x, ψ.map x = f x) :
    φ.map = ψ.map := by
  funext x
  rw [hφ, hψ]

end StructureTower

/-! ## 積の普遍性 (Version B) -/

/-- 直積構造塔 -/
def StructureTower.prod (T₁ T₂ : StructureTower) : StructureTower where
  carrier := T₁.carrier × T₂.carrier
  Index := T₁.Index × T₂.Index
  indexPreorder := inferInstanceAs (Preorder (T₁.Index × T₂.Index))
  layer := fun ⟨i, j⟩ => T₁.layer i ×ˢ T₂.layer j
  covering := by
    intro ⟨x₁, x₂⟩
    obtain ⟨i, hi⟩ := T₁.covering x₁
    obtain ⟨j, hj⟩ := T₂.covering x₂
    exact ⟨⟨i, j⟩, ⟨hi, hj⟩⟩
  monotone := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ ⟨hi, hj⟩ ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨T₁.monotone hi hx, T₂.monotone hj hy⟩

namespace StructureTower

variable {T T₁ T₂ : StructureTower}

def proj₁ (T₁ T₂ : StructureTower) :
    Hom (prod T₁ T₂) T₁ where
  map := Prod.fst
  indexMap := Prod.fst
  indexMap_mono := fun h => h.1
  layer_preserving := fun _ _ h => h.1

def proj₂ (T₁ T₂ : StructureTower) :
    Hom (prod T₁ T₂) T₂ where
  map := Prod.snd
  indexMap := Prod.snd
  indexMap_mono := fun h => h.2
  layer_preserving := fun _ _ h => h.2

/-- 積への普遍射の構成 -/
def prodUniversal (f₁ : Hom T T₁) (f₂ : Hom T T₂) :
    Hom T (prod T₁ T₂) where
  map := fun x => ⟨f₁.map x, f₂.map x⟩
  indexMap := fun i => ⟨f₁.indexMap i, f₂.indexMap i⟩
  indexMap_mono := by
    intro i j hij
    exact ⟨f₁.indexMap_mono hij, f₂.indexMap_mono hij⟩
  layer_preserving := by
    intro i x hx
    exact ⟨f₁.layer_preserving i x hx, f₂.layer_preserving i x hx⟩

/-- 【証明可能】普遍射が射影と可換 -/
theorem prodUniversal_proj₁ (f₁ : Hom T T₁) (f₂ : Hom T T₂) :
    Hom.comp (proj₁ T₁ T₂) (prodUniversal f₁ f₂) = f₁ := by
  rfl

theorem prodUniversal_proj₂ (f₁ : Hom T T₁) (f₂ : Hom T T₂) :
    Hom.comp (proj₂ T₁ T₂) (prodUniversal f₁ f₂) = f₂ := by
  rfl

/-- 【Version B】基礎写像に関しては一意
（射としては一意でない） -/
theorem prodUniversal_unique_map (f₁ : Hom T T₁) (f₂ : Hom T T₂)
    (g : Hom T (prod T₁ T₂))
    (h₁ : Hom.comp (proj₁ T₁ T₂) g = f₁)
    (h₂ : Hom.comp (proj₂ T₁ T₂) g = f₂) :
    g.map = (prodUniversal f₁ f₂).map := by
  funext x
  have : g.map x =
      ⟨(Hom.comp (proj₁ T₁ T₂) g).map x,
        (Hom.comp (proj₂ T₁ T₂) g).map x⟩ := rfl
  rw [h₁, h₂] at this
  exact this

end StructureTower

/- ======================================================================
   Version C: 分離された構造塔（層が交わらない）
   ====================================================================== -/

/-- 分離された構造塔：各要素が正確に1つの層に属する -/
structure SeparatedStructureTower where
  carrier : Type*
  Index : Type*
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- 分離条件：i ≠ j なら層は素 -/
  separated : ∀ i j, i ≠ j → Disjoint (layer i) (layer j)

/-
注意：この定義は非常に制限的で、多くの自然な構造塔（実数区間など）を除外します。
教育的には興味深いですが、実用性は低いです。
-/

/-! ## まとめと推奨事項 -/

/-
### どのバージョンを使うべきか？

**学習目的なら:**
- **Version A (StructureTowerWithMin)** を推奨
  - 完全な一意性を持つ普遍性が証明可能
  - minLayer の概念は自然で直感的
  - 多くの応用で実用的

**研究・一般理論なら:**
- **Version B (StructureTower)** を推奨
  - より一般的な定義
  - 「基礎写像の一意性」が正しい定式化
  - indexMap の非一意性を認識することが重要

**特殊な場合なら:**
- **Version C (SeparatedStructureTower)** 
  - 非常に制限的だが単純
  - 完全な一意性が自動的に成り立つ
  - 実用性は限定的

### 数学的教訓

この問題は以下を示しています：

1. **形式化の際には隠れた仮定に注意**
   非形式的な数学では「自然に選べる」と思っている操作が、
   実は選択の自由度を持つことがある

2. **普遍性には適切なレベルがある**
   「射として一意」vs「基礎写像として一意」の区別

3. **定義の選択がトレードオフを生む**
   一般性 vs 証明の容易さ

このような問題に気づいて指摘できることが、優れた形式化者の証です！
-/

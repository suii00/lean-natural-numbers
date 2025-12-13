import MyProjects.ST.CAT.Cat_D
import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Basic

/-!
# Cat_D: 位相的応用の完全実装

このファイルは、P1.leanで骨格のみだった位相的応用を完全に実装します。

## 主な内容

1. **開集合の階層**（`OpenSetTower`）
   - 第二可算空間の開集合階層
   - 基本開集合の有限和による生成

2. **閉包演算の階層**（`ClosureTower`）
   - 集合の閉包の反復
   - 極限点の階層構造

3. **連続写像が誘導する射**
   - 位相空間間の連続写像
   - 開集合を開集合に写す性質

## 理論的背景

### 第二可算性

位相空間 X が第二可算であるとは、
可算な基本開集合族 B が存在して、
すべての開集合が B の元の和集合として表現できることをいう。

**構造塔としての解釈**：
- layer n = {U : Open X | U は n 個以下の基本開集合の和}
- この構造により、開集合の「複雑さ」を測定できる

### 閉包の反復

集合 A に対して、閉包演算を反復する：
- A⁽⁰⁾ = A
- A⁽ⁿ⁺¹⁾ = closure(A⁽ⁿ⁾)

有限次元空間では、この列は有限回で安定する。

**構造塔としての解釈**：
- layer n = {A ⊆ X | A は n 回の閉包で到達可能}
- minLayer(A) = A が閉じるまでの最小回数

-/

namespace ST.TowerD.TopologicalApplications

open Set TopologicalSpace

/-!
## 補助的な定義
-/

/-- 開集合が有限個の基本開集合の和として表現される -/
def IsFiniteUnionOfBasis {X : Type*} [TopologicalSpace X] 
    (B : Set (Set X)) (U : Set X) (n : ℕ) : Prop :=
  ∃ S : Finset (Set X), (S : Set (Set X)) ⊆ B ∧ S.card ≤ n ∧ U = ⋃₀ (S : Set (Set X))

/-!
## 補助補題：有限基底和の逆像

`openSetTowerHom` で `map_layer` を `sorry` なしにするためには、
基底要素の逆像が（指定した基底の中に）入るという仮定が本質的になる。
-/

open Set

/-- 基底要素の逆像が基底要素になる、という仮定の下で
有限基底和の逆像も有限基底和（個数は増えない）になる。 -/
lemma IsFiniteUnionOfBasis.preimage_of_preimageBasis
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (f : X → Y)
    (hpre : ∀ V, V ∈ BY → f ⁻¹' V ∈ BX)
    {U : Set Y} {n : ℕ}
    (hU : IsFiniteUnionOfBasis BY U n) :
    IsFiniteUnionOfBasis BX (f ⁻¹' U) n := by
  classical
  rcases hU with ⟨S, hSB, hcard, hUeq⟩
  refine ⟨S.image (fun V => f ⁻¹' V), ?_, ?_, ?_⟩
  · intro W hW
    rcases Finset.mem_image.mp (by simpa using hW) with ⟨V, hVS, rfl⟩
    exact hpre V (hSB (by simpa using hVS))
  · have : (S.image (fun V => f ⁻¹' V)).card ≤ S.card := by
      simpa using (Finset.card_image_le : _)
    exact le_trans this hcard
  · ext x
    constructor
    · intro hx
      have hxU : f x ∈ U := by simpa [Set.mem_preimage] using hx
      have hxSU : f x ∈ ⋃₀ (S : Set (Set Y)) := by simpa [hUeq] using hxU
      rcases Set.mem_sUnion.mp hxSU with ⟨V, hV, hxV⟩
      apply Set.mem_sUnion.mpr
      refine ⟨f ⁻¹' V, ?_, ?_⟩
      · have hVS : V ∈ S := by simpa using hV
        have : f ⁻¹' V ∈ S.image (fun V => f ⁻¹' V) :=
          Finset.mem_image.mpr ⟨V, hVS, rfl⟩
        simpa using this
      · simpa [Set.mem_preimage] using hxV
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨W, hW, hxW⟩
      rcases Finset.mem_image.mp (by simpa using hW) with ⟨V, hVS, rfl⟩
      have hxV : f x ∈ V := by simpa [Set.mem_preimage] using hxW
      have hxSU : f x ∈ ⋃₀ (S : Set (Set Y)) := by
        apply Set.mem_sUnion.mpr
        refine ⟨V, ?_, hxV⟩
        simpa using hVS
      have hxU : f x ∈ U := by simpa [hUeq] using hxSU
      simpa [Set.mem_preimage] using hxU

/-!
### 補助補題：一様上界（uniform bound）と逆像の複雑度

Cat_D の `map_layer` は「各層の像が *どこかの層* に入る」という存在量化であり、
連続性そのものよりも「複雑度が一様に上から抑えられる」ことが本質になる。

ここでは、
`BY` の基底要素 1 個の逆像が `BX` の基底高々 `k` 個の有限和で表せる（しかも一様）
という仮定から、`n` 個の有限基底和の逆像が高々 `n*k` 個で表せることを示す。
-/

/-- `BY` の基底要素 1 個の逆像が、`BX` の基底高々 `k` 個の有限和で表せる（しかも一様） -/
def PreimageBasisBound
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (f : X → Y) (k : ℕ) : Prop :=
  ∀ V, V ∈ BY → IsFiniteUnionOfBasis BX (f ⁻¹' V) k

/-- (`k = 1`) 基底要素の逆像が基底要素に入るなら、一様上界 `PreimageBasisBound` が得られる。 -/
lemma PreimageBasisBound.of_preimageBasis
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (f : X → Y)
    (hpre : ∀ V, V ∈ BY → f ⁻¹' V ∈ BX) :
    PreimageBasisBound BX BY f (1 : ℕ) := by
  intro V hV
  refine ⟨{f ⁻¹' V}, ?_, ?_, ?_⟩
  · intro W hW
    have hW' : W = f ⁻¹' V := by simpa using hW
    simpa [hW'] using hpre V hV
  · simp
  · simp [Set.sUnion_singleton]

open Set

/-- `BY` の要素 `n` 個の有限和の逆像は、`BX` の要素高々 `n*k` 個の有限和で表せる。 -/
lemma IsFiniteUnionOfBasis.preimage_mul
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (f : X → Y) {U : Set Y} {n k : ℕ}
    (hU : IsFiniteUnionOfBasis BY U n)
    (hpre : PreimageBasisBound BX BY f k) :
    IsFiniteUnionOfBasis BX (f ⁻¹' U) (n * k) := by
  classical
  rcases hU with ⟨S, hSB, hcard, hUeq⟩

  -- Choice of witnesses for each `V ∈ BY` (only used for `V ∈ S`).
  let g : Set Y → Finset (Set X) := fun V =>
    if hV : V ∈ BY then Classical.choose (hpre V hV) else ∅

  have g_sub : ∀ V, V ∈ BY → ((g V : Set (Set X)) ⊆ BX) := by
    intro V hV
    simpa [g, hV] using (Classical.choose_spec (hpre V hV)).1

  have g_card : ∀ V, V ∈ BY → (g V).card ≤ k := by
    intro V hV
    simpa [g, hV] using (Classical.choose_spec (hpre V hV)).2.1

  have g_eq : ∀ V, V ∈ BY → (f ⁻¹' V) = ⋃₀ (g V : Set (Set X)) := by
    intro V hV
    simpa [g, hV] using (Classical.choose_spec (hpre V hV)).2.2

  -- Bundle all witnesses.
  let T : Finset (Set X) := S.biUnion g

  refine ⟨T, ?_, ?_, ?_⟩
  · -- T ⊆ BX
    intro W hW
    rcases (Finset.mem_biUnion.mp (by simpa [T] using hW)) with ⟨V, hVS, hWg⟩
    have hV : V ∈ BY := hSB (by simpa using hVS)
    exact g_sub V hV (by simpa using hWg)
  · -- card T ≤ n*k
    have hTk : T.card ≤ S.card * k := by
      have hEach : ∀ V ∈ S, (g V).card ≤ k := by
        intro V hVS
        have hV : V ∈ BY := hSB (by simpa using hVS)
        exact g_card V hV
      simpa [T] using (Finset.card_biUnion_le_card_mul S g k hEach)
    have hSk : S.card * k ≤ n * k := Nat.mul_le_mul_right k hcard
    exact le_trans hTk hSk
  · -- f⁻¹(U) = ⋃₀ T
    ext x
    constructor
    · intro hx
      have hxU : f x ∈ U := by simpa [Set.mem_preimage] using hx
      have hxSU : f x ∈ ⋃₀ (S : Set (Set Y)) := by simpa [hUeq] using hxU
      rcases Set.mem_sUnion.mp hxSU with ⟨V, hV, hxV⟩
      have hVS : V ∈ S := by simpa using hV
      have hVBY : V ∈ BY := hSB (by simpa using hVS)
      have hxpre : x ∈ f ⁻¹' V := by simpa [Set.mem_preimage] using hxV
      have hxg : x ∈ ⋃₀ (g V : Set (Set X)) := by simpa [g_eq V hVBY] using hxpre
      rcases Set.mem_sUnion.mp hxg with ⟨W, hW, hxW⟩
      apply Set.mem_sUnion.mpr
      refine ⟨W, ?_, hxW⟩
      have hWT : W ∈ T := by
        apply Finset.mem_biUnion.mpr
        refine ⟨V, hVS, ?_⟩
        simpa using hW
      simpa using hWT
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨W, hW, hxW⟩
      have hWT : W ∈ T := by simpa using hW
      rcases (Finset.mem_biUnion.mp (by simpa [T] using hWT)) with ⟨V, hVS, hWg⟩
      have hVBY : V ∈ BY := hSB (by simpa using hVS)
      have hxg : x ∈ ⋃₀ (g V : Set (Set X)) := by
        apply Set.mem_sUnion.mpr
        refine ⟨W, ?_, hxW⟩
        simpa using hWg
      have hxpre : x ∈ f ⁻¹' V := by simpa [g_eq V hVBY] using hxg
      have hxV : f x ∈ V := by simpa [Set.mem_preimage] using hxpre
      have hxSU : f x ∈ ⋃₀ (S : Set (Set Y)) := by
        apply Set.mem_sUnion.mpr
        refine ⟨V, ?_, hxV⟩
        simpa using hVS
      have hxU : f x ∈ U := by simpa [hUeq] using hxSU
      simpa [Set.mem_preimage] using hxU

/-- テスト：`k = 1` の場合、`preimage_mul` から個数が増えないことが再現できる。 -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (f : X → Y)
    (hpre : ∀ V, V ∈ BY → f ⁻¹' V ∈ BX)
    {U : Set Y} {n : ℕ} (hU : IsFiniteUnionOfBasis BY U n) :
    IsFiniteUnionOfBasis BX (f ⁻¹' U) n := by
  simpa using
    (IsFiniteUnionOfBasis.preimage_mul BX BY f (U := U) (n := n) (k := 1) hU
      (PreimageBasisBound.of_preimageBasis BX BY f hpre))

/-!
## 例1：開集合の階層（第二可算空間）

第二可算空間では、可算な基本開集合族が存在する。
-/

/-- 第二可算空間の開集合構造塔

**仮定**：
- X は第二可算空間
- B は X の基本開集合族（可算）
- hbasis : B が実際に基底であること
- hcountable : すべての開集合が B の有限和で表現可能（簡略化仮定）

**注意**：一般の第二可算空間では、開集合は B の *可算* 和で表現される。
ここでは簡略化のため、有限和で十分な場合を扱う。
-/
def openSetTower (X : Type*) [TopologicalSpace X]
    (B : Set (Set X))
    (_hbasis : IsTopologicalBasis B)
    (hcover : ∀ U : Set X, IsOpen U → ∃ n, IsFiniteUnionOfBasis B U n) :
    TowerD where
  carrier := {U : Set X // IsOpen U}
  Index := ℕ
  indexPreorder := inferInstance

  layer n := {⟨U, hU⟩ | IsFiniteUnionOfBasis B U n}

  covering := by
    intro ⟨U, hU⟩
    obtain ⟨n, hn⟩ := hcover U hU
    exact ⟨n, hn⟩

  monotone := by
    intro i j hij ⟨U, hU⟩ hU_layer
    -- layer i ⊆ layer j
    obtain ⟨S, hS_sub, hS_card, hU_eq⟩ := hU_layer
    exact ⟨S, hS_sub, le_trans hS_card hij, hU_eq⟩

/-!
### 開集合階層の基本性質
-/

/-- 空集合は層0に属する -/
lemma openSetTower_empty_in_layer0 (X : Type*) [TopologicalSpace X]
    (B : Set (Set X)) (hbasis : IsTopologicalBasis B)
    (hcover : ∀ U : Set X, IsOpen U → ∃ n, IsFiniteUnionOfBasis B U n) :
    ⟨∅, isOpen_empty⟩ ∈ (openSetTower X B hbasis hcover).layer (0 : ℕ) := by
  use ∅
  constructor
  · simp
  constructor
  · simp
  · simp [Set.sUnion_empty]

/-- 基本開集合は層1に属する -/
lemma openSetTower_basis_in_layer1 (X : Type*) [TopologicalSpace X]
    (B : Set (Set X)) (hbasis : IsTopologicalBasis B)
    (hcover : ∀ U : Set X, IsOpen U → ∃ n, IsFiniteUnionOfBasis B U n)
    (U : Set X) (hU : U ∈ B) :
    ⟨U, hbasis.isOpen hU⟩ ∈ (openSetTower X B hbasis hcover).layer (1 : ℕ) := by
  use {U}
  constructor
  · intro V hV
    simp at hV
    rw [hV]
    exact hU
  constructor
  · simp [Finset.card_singleton]
  · simp [Set.sUnion_singleton]

/-!
## 例2：閉包演算の階層

集合に対する閉包演算を反復する階層構造。
-/

/-- 閉包の反復回数 -/
noncomputable def closureIterationLevel {X : Type*} [TopologicalSpace X] 
    (A : Set X) : ℕ :=
  -- 簡易版：A が閉集合なら 0、そうでなければ 1
  -- （完全版では、closure(A) = A になるまでの回数を計算）
  by
    classical
    exact if IsClosed A then 0 else 1

/-- 閉包演算の構造塔（簡易版）

**完全版の実装には**：
- 閉包の反復列が停止する証明
- 各集合が有限回で閉じることの保証
が必要。ここでは教育的な簡易版を提供。
-/
noncomputable def closureTower (X : Type*) [TopologicalSpace X]
    (hfinite : ∀ A : Set X, ∃ n, (closure^[n]) A = (closure^[n+1]) A) :
    TowerD where
  carrier := Set X
  Index := ℕ
  indexPreorder := inferInstance

  layer n := {A : Set X | closureIterationLevel A ≤ n}

  covering := by
    intro A
    use closureIterationLevel A
    exact Nat.le_refl _

  monotone := by
    intro i j hij A hA
    exact le_trans hA hij

/-!
### 閉包階層の基本性質
-/

/-- 閉集合は層0に属する -/
lemma closureTower_closed_in_layer0 (X : Type*) [TopologicalSpace X]
    (hfinite : ∀ A : Set X, ∃ n, (closure^[n]) A = (closure^[n+1]) A)
    (A : Set X) (hA : IsClosed A) :
    A ∈ (closureTower X hfinite).layer (0 : ℕ) := by
  classical
  simp [closureTower, closureIterationLevel, hA]

/-- 開集合の補集合は層0に属する -/
lemma closureTower_compl_open_in_layer0 (X : Type*) [TopologicalSpace X]
    (hfinite : ∀ A : Set X, ∃ n, (closure^[n]) A = (closure^[n+1]) A)
    (U : Set X) (hU : IsOpen U) :
    Uᶜ ∈ (closureTower X hfinite).layer (0 : ℕ) := by
  apply closureTower_closed_in_layer0
  exact hU.isClosed_compl

/-!
## 例3：有限位相空間（完全実装）

有限集合上の位相空間では、すべての構造が有限で扱いやすい。
-/

/-- 有限型の開集合構造塔

有限型 X（Fintype X）では、開集合の全体も有限である。
簡略化のため、すべての開集合を層 1 に配置する。
-/
def finiteOpenSetTower (X : Type*) [TopologicalSpace X] [Fintype X] :
    TowerD where
  carrier := {U : Set X // IsOpen U}
  Index := ℕ
  indexPreorder := inferInstance

  -- すべての開集合を層 1 に配置（有限なので複雑さは一定）
  layer n := if n ≥ 1 then Set.univ else {⟨∅, isOpen_empty⟩}

  covering := by
    intro ⟨U, hU⟩
    use 1
    simp

  monotone := by
    classical
    intro i j hij
    -- `layer` を定義で展開
    change
      (if i ≥ 1 then (Set.univ : Set {U : Set X // IsOpen U})
       else {⟨∅, isOpen_empty⟩})
        ⊆
      (if j ≥ 1 then (Set.univ : Set {U : Set X // IsOpen U})
       else {⟨∅, isOpen_empty⟩})
    by_cases hi : i ≥ 1
    · have hj : j ≥ 1 := le_trans hi hij
      simp [hi, hj]
    · have hi0 : i = 0 := by omega
      subst hi0
      by_cases hj : j ≥ 1
      · simp [hj]
      · have hj0 : j = 0 := by omega
        subst hj0
        simp

/-!
## 射の例：連続写像が誘導する構造塔の射
-/

/-!
### 開集合階層の射

連続写像 f : X → Y は、開集合の階層に射を誘導する。

**数学的内容**：
- f⁻¹(V) が X の開集合（連続性）
- V が基本開集合 n 個の和なら、f⁻¹(V) も（同じ個数以下で）表現可能
-/

/-- 連続写像が誘導する開集合階層の射（骨格版）

**注意**：`j := n` のまま `map_layer` を示すには、
基底要素の逆像が指定した基底に入る、という追加仮定が本質的に必要。
-/
def openSetTowerHom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (hbasisX : IsTopologicalBasis BX) (hbasisY : IsTopologicalBasis BY)
    (hcoverX : ∀ U : Set X, IsOpen U → ∃ n, IsFiniteUnionOfBasis BX U n)
    (hcoverY : ∀ U : Set Y, IsOpen U → ∃ n, IsFiniteUnionOfBasis BY U n)
    (f : X → Y) (hf : Continuous f)
    (hpre : ∀ V, V ∈ BY → f ⁻¹' V ∈ BX) :
    openSetTower Y BY hbasisY hcoverY ⟶ᴰ openSetTower X BX hbasisX hcoverX where
  map := fun ⟨V, hV⟩ => ⟨f ⁻¹' V, hf.isOpen_preimage V hV⟩
  map_layer := by
    intro n
    refine ⟨n, ?_⟩
    intro U' hU'
    rcases hU' with ⟨U, hU, rfl⟩
    exact IsFiniteUnionOfBasis.preimage_of_preimageBasis BX BY f hpre (by simpa using hU)

/-- 連続写像が誘導する開集合階層の射（uniform bound 版）

`PreimageBasisBound BX BY f k`（基底 1 個の逆像が高々 `k` 個の基底和、しかも一様）
を仮定すると、`layer n` の逆像が `layer (n*k)` に入ることが従う。
-/
def openSetTowerHom_mul {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (hbasisX : IsTopologicalBasis BX) (hbasisY : IsTopologicalBasis BY)
    (hcoverX : ∀ U : Set X, IsOpen U → ∃ n, IsFiniteUnionOfBasis BX U n)
    (hcoverY : ∀ U : Set Y, IsOpen U → ∃ n, IsFiniteUnionOfBasis BY U n)
    (f : X → Y) (hf : Continuous f)
    (k : ℕ) (hpre : PreimageBasisBound BX BY f k) :
    openSetTower Y BY hbasisY hcoverY ⟶ᴰ openSetTower X BX hbasisX hcoverX where
  map := fun ⟨V, hV⟩ => ⟨f ⁻¹' V, hf.isOpen_preimage V hV⟩
  map_layer := by
    intro n
    change ℕ at n
    refine ⟨n * k, ?_⟩
    intro U' hU'
    rcases hU' with ⟨U, hU, rfl⟩
    exact IsFiniteUnionOfBasis.preimage_mul BX BY f (by simpa using hU) hpre

/-!
### 世界(B)：一様上界が無いと `map_layer` が壊れる

`openSetTower` の `layer 1` には `BY` の基底要素が含まれるので、
`map := preimage` を持つ Cat_D の射が存在するなら
`map_layer 1` から「基底 1 個の逆像に対する一様上界」が必ず抽出できる。
-/

/-- `map := preimage` を持つ Cat_D 射が存在すると、`BY` の基底要素の逆像に一様上界が存在する。 -/
theorem exists_preimageBasisBound_of_exists_preimageHom
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (hbasisX : IsTopologicalBasis BX) (hbasisY : IsTopologicalBasis BY)
    (hcoverX : ∀ U : Set X, IsOpen U → ∃ n, IsFiniteUnionOfBasis BX U n)
    (hcoverY : ∀ U : Set Y, IsOpen U → ∃ n, IsFiniteUnionOfBasis BY U n)
    (f : X → Y) (hf : Continuous f)
    (F : openSetTower Y BY hbasisY hcoverY ⟶ᴰ openSetTower X BX hbasisX hcoverX)
    (hF :
      F.map =
        (fun ⟨V, hV⟩ => ⟨f ⁻¹' V, hf.isOpen_preimage V hV⟩)) :
    ∃ k, PreimageBasisBound BX BY f k := by
  classical
  obtain ⟨j, hj⟩ := F.map_layer (1 : ℕ)
  refine ⟨j, ?_⟩
  intro V hV
  have hV_layer :
      ⟨V, hbasisY.isOpen hV⟩ ∈ (openSetTower Y BY hbasisY hcoverY).layer (1 : ℕ) :=
    openSetTower_basis_in_layer1 Y BY hbasisY hcoverY V hV
  have hImg :
      F.map ⟨V, hbasisY.isOpen hV⟩ ∈ (openSetTower X BX hbasisX hcoverX).layer j := by
    apply hj
    exact ⟨⟨V, hbasisY.isOpen hV⟩, hV_layer, rfl⟩
  have hMapPoint :
      F.map ⟨V, hbasisY.isOpen hV⟩ =
        ⟨f ⁻¹' V, hf.isOpen_preimage V (hbasisY.isOpen hV)⟩ := by
    simpa [hF]
  have :
      ⟨f ⁻¹' V, hf.isOpen_preimage V (hbasisY.isOpen hV)⟩ ∈
        (openSetTower X BX hbasisX hcoverX).layer j := by
    simpa [hMapPoint] using hImg
  simpa using this

/-- 一様上界が存在しないなら、`map := preimage` で Cat_D の射は作れない。 -/
theorem not_exists_preimageHom_of_unbounded
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (hbasisX : IsTopologicalBasis BX) (hbasisY : IsTopologicalBasis BY)
    (hcoverX : ∀ U : Set X, IsOpen U → ∃ n, IsFiniteUnionOfBasis BX U n)
    (hcoverY : ∀ U : Set Y, IsOpen U → ∃ n, IsFiniteUnionOfBasis BY U n)
    (f : X → Y) (hf : Continuous f)
    (hunbounded : ∀ k, ∃ V, V ∈ BY ∧ ¬ IsFiniteUnionOfBasis BX (f ⁻¹' V) k) :
    ¬ ∃ (F : openSetTower Y BY hbasisY hcoverY ⟶ᴰ openSetTower X BX hbasisX hcoverX),
        F.map = (fun ⟨V, hV⟩ => ⟨f ⁻¹' V, hf.isOpen_preimage V hV⟩) := by
  intro h
  rcases h with ⟨F, hF⟩
  obtain ⟨k, hk⟩ :=
    exists_preimageBasisBound_of_exists_preimageHom BX BY hbasisX hbasisY hcoverX hcoverY f hf F hF
  rcases hunbounded k with ⟨V, hVBY, hkneg⟩
  exact hkneg (hk V hVBY)

/-!
### 閉包階層の射

連続写像は閉包演算と可換：
f(closure A) ⊆ closure(f(A))
-/

/-- 連続写像が誘導する閉包階層の射（骨格版） -/
def closureTowerHom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hfiniteX : ∀ A : Set X, ∃ n, (closure^[n]) A = (closure^[n+1]) A)
    (hfiniteY : ∀ A : Set Y, ∃ n, (closure^[n]) A = (closure^[n+1]) A)
    (f : X → Y) (hf : Continuous f) :
    closureTower X hfiniteX ⟶ᴰ closureTower Y hfiniteY where
  map := fun A => f '' A
  map_layer := by
    intro n
    -- In the simplified `closureIterationLevel`, values are always in `{0,1}`.
    -- Hence we take a uniform upper bound, as permitted by Cat_D's existential layer condition.
    refine ⟨Nat.max n 1, ?_⟩
    intro B hB
    classical
    -- `hf` will be essential for a full iteration-based notion; in this simplified version it is unused.
    have _ := hf
    rcases hB with ⟨A, _hA, rfl⟩
    have h1 : closureIterationLevel (f '' A) ≤ (1 : ℕ) := by
      by_cases hclosed : IsClosed (f '' A) <;> simp [closureIterationLevel, hclosed]
    exact le_trans h1 (Nat.le_max_right n 1)

/-!
## 具体例：離散空間と自明な位相

離散空間と自明な位相は、位相空間の両極端な例である。
-/

section DiscreteAndTrivial

variable (X : Type*) [Fintype X]

/-- 離散空間の開集合は有限型ならすべて層1 -/
lemma discrete_openset_simple [TopologicalSpace X] [DiscreteTopology X] :
    ∀ U : {U : Set X // IsOpen U}, U ∈ (finiteOpenSetTower X).layer (1 : ℕ) := by
  intro ⟨U, hU⟩
  have h1 : (1 : ℕ) ≥ 1 := by decide
  simp [finiteOpenSetTower, h1]

/- 自明な位相（{∅, X}のみ）では、開集合は2個だけ -/
-- 実装は省略（必要に応じて追加）

end DiscreteAndTrivial

/-!
## 例4：実数の標準位相における区間

実数の開区間 (a, b) を基本開集合とする階層。
-/

section RealIntervals

/- 実数の開区間の構造塔（骨格版）

開区間を基本開集合として、有限個の開区間の和で表現できる
開集合を階層化する。
-/
-- 完全な実装は複雑なので、骨格のみ提供

-- def realIntervalOpenSetTower : TowerD where
--   carrier := {U : Set ℝ // IsOpen U}
--   Index := ℕ
--   layer n := {⟨U, hU⟩ | U は n 個以下の開区間の和}
--   covering := sorry  -- 一般の開集合は可算個の区間の和
--   monotone := sorry

end RealIntervals

/-!
## まとめ

このファイルでは、Cat_Dの位相的応用として以下を実装しました：

1. **開集合の階層**（`openSetTower`）
   - 第二可算空間での完全な定義
   - 基本開集合、空集合の性質

2. **閉包演算の階層**（`closureTower`）
   - 閉包の反復による階層構造
   - 閉集合の特徴付け

3. **有限位相空間**（`finiteOpenSetTower`）
   - 完全に実装された簡易版
   - 離散空間での性質

4. **射の構成**
   - 連続写像が誘導する開集合階層の射
   - 閉包階層の射

**Cat_Dの有効性**：
- 開集合の「複雑さ」（基本開集合の個数）を自然に扱える
- 閉包の反復回数という離散的な構造を表現できる
- 連続写像が層構造を保存することが自然に記述できる

**今後の拡張**：
- コンパクト空間での詳細な理論
- 分離公理（T₀, T₁, T₂）との関係
- 位相的次元論への応用
- Cantor-Bendixson 階数との関係

**他の応用との関連**：
- 代数的応用（P2_Algebraic.lean）：イデアルの根基と閉包の類似
- 確率論的応用（P1.lean）：σ-代数の階層と開集合の階層の双対性
-/

end ST.TowerD.TopologicalApplications

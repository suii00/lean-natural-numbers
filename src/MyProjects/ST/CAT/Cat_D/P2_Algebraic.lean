import MyProjects.ST.CAT.Cat_D
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.EuclideanDomain.Int

instance instIsPrincipalIdealRingInt : IsPrincipalIdealRing ℤ :=
  EuclideanDomain.to_principal_ideal_domain (R := ℤ)

/-!
# Cat_D: 代数的応用の完全実装

このファイルは、P1.leanで骨格のみだった代数的応用を完全に実装します。

## 主な内容

1. **部分群の階層**（`SubgroupTower`）
   - 有限生成部分群の階層構造
   - 生成元の個数による層別

2. **イデアルの階層**（`IdealTower`）
   - Noether環のイデアルの階層
   - 生成元の個数による層別

3. **射の例**
   - 群準同型が誘導する部分群階層の射
   - 環準同型が誘導するイデアル階層の射

## 理論的背景

### 部分群の有限生成性

群 G の部分群 H が有限生成であるとは、
有限集合 S ⊆ G が存在して H = ⟨S⟩ となることをいう。

**構造塔としての解釈**：
- layer n = {H ≤ G | ∃ S : Finset G, |S| ≤ n ∧ H = ⟨S⟩}
- minLayer(H) = H を生成する最小の基底の濃度

### Noether環のイデアル

環 R が Noether 環であるとは、すべてのイデアルが有限生成であることをいう。

**構造塔としての解釈**：
- layer n = {I ⊴ R | ∃ S : Finset R, |S| ≤ n ∧ I = Ideal.span S}
- minLayer(I) = I を生成する最小の元の個数

-/

namespace ST.TowerD.AlgebraicApplications

open Set Subgroup Ideal

/-!
## 補助的な定義：有限生成性
-/

/-- 部分群が有限集合で生成される -/
def _root_.Subgroup.IsFinGenBy {G : Type*} [Group G] (H : Subgroup G) (S : Finset G) : Prop :=
  H = Subgroup.closure (S : Set G)

/-- 部分群が有限生成である -/
def _root_.Subgroup.IsFinitelyGenerated {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Finset G, H.IsFinGenBy S

/-- イデアルが有限集合で生成される -/
def _root_.Ideal.IsFinGenBy {R : Type*} [CommRing R] (I : Ideal R) (S : Finset R) : Prop :=
  I = Ideal.span (S : Set R)

/-- イデアルが有限生成である -/
def _root_.Ideal.IsFinitelyGenerated {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∃ S : Finset R, I.IsFinGenBy S

/-- `Subgroup.map` と `closure` の交換（再掲） -/
lemma subgroup_map_closure {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (s : Set G) :
    (Subgroup.closure s).map φ = Subgroup.closure (φ '' s) :=
by
  -- mathlib の証明をそのまま利用
  simpa using
    (Set.image_preimage.l_comm_of_u_comm
      (gc_map_comap φ) (Subgroup.gi G').gc (Subgroup.gi G).gc (fun _ => rfl))

/-!
## 例1：部分群の階層構造塔

有限生成群（すべての部分群が有限生成）を仮定する。
-/

/-- 有限生成群の構造塔

**注意**：一般の群では、すべての部分群が有限生成とは限らない。
ここでは covering のために「すべての部分群が有限生成」を仮定する。

典型的な例：
- 有限群（すべての部分群は自動的に有限生成）
- 自由群 F_n（有限ランクの場合）
- アーベル群 ℤⁿ
-/
def subgroupTower (G : Type*) [Group G]
    (hfg : ∀ H : Subgroup G, H.IsFinitelyGenerated) : TowerD where
  carrier := Subgroup G
  Index := ℕ
  indexPreorder := inferInstance

  layer n := {H : Subgroup G | ∃ S : Finset G, S.card ≤ n ∧ H.IsFinGenBy S}

  covering := by
    intro H
    -- 仮定により H は有限生成
    obtain ⟨S, hS⟩ := hfg H
    use S.card
    exact ⟨S, le_rfl, hS⟩

  monotone := by
    intro i j hij H hH
    -- H ∈ layer i ⇒ H ∈ layer j
    obtain ⟨S, hcard, hgen⟩ := hH
    exact ⟨S, le_trans hcard hij, hgen⟩

/-!
### 部分群階層の基本性質
-/

/-- 自明な部分群は層0に属する -/
lemma subgroupTower_bot_in_layer0 (G : Type*) [Group G]
    (hfg : ∀ H : Subgroup G, H.IsFinitelyGenerated) :
    (⊥ : Subgroup G) ∈ (subgroupTower G hfg).layer (0 : ℕ) := by
  use ∅
  constructor
  · simp
  · simp [Subgroup.IsFinGenBy, Subgroup.closure_empty]

/-- 巡回部分群は層1に属する -/
lemma subgroupTower_cyclic_in_layer1 (G : Type*) [Group G]
    (hfg : ∀ H : Subgroup G, H.IsFinitelyGenerated)
    (g : G) :
    Subgroup.closure {g} ∈ (subgroupTower G hfg).layer (1 : ℕ) := by
  classical
  refine ⟨{g}, ?_, ?_⟩
  · simp [Finset.card_singleton]
  · simp [Subgroup.IsFinGenBy]

/-!
## 例2：Noether環のイデアル階層

Noether環では、すべてのイデアルが有限生成である。
-/

/-- Noether環のイデアル構造塔

**Noether環の定義**：すべてのイデアルが有限生成
-/
def idealTower (R : Type*) [CommRing R]
    (hnoether : ∀ I : Ideal R, I.IsFinitelyGenerated) : TowerD where
  carrier := Ideal R
  Index := ℕ
  indexPreorder := inferInstance

  layer n := {I : Ideal R | ∃ S : Finset R, S.card ≤ n ∧ I.IsFinGenBy S}

  covering := by
    intro I
    obtain ⟨S, hS⟩ := hnoether I
    use S.card
    exact ⟨S, le_rfl, hS⟩

  monotone := by
    intro i j hij I hI
    obtain ⟨S, hcard, hgen⟩ := hI
    exact ⟨S, le_trans hcard hij, hgen⟩

/-!
### イデアル階層の基本性質
-/

/-- 零イデアルは層0に属する -/
lemma idealTower_bot_in_layer0 (R : Type*) [CommRing R]
    (hnoether : ∀ I : Ideal R, I.IsFinitelyGenerated) :
    (⊥ : Ideal R) ∈ (idealTower R hnoether).layer (0 : ℕ) := by
  use ∅
  constructor
  · simp
  · simp [Ideal.IsFinGenBy, Ideal.span_empty]

/-- 単項イデアルは層1に属する -/
lemma idealTower_principal_in_layer1 (R : Type*) [CommRing R]
    (hnoether : ∀ I : Ideal R, I.IsFinitelyGenerated)
    (r : R) :
    Ideal.span {r} ∈ (idealTower R hnoether).layer (1 : ℕ) := by
  classical
  refine ⟨{r}, ?_, ?_⟩
  · simp [Finset.card_singleton]
  · simp [Ideal.IsFinGenBy]

/-- 単項イデアル整域（PID）では、すべてのイデアルが層1に属する -/
lemma idealTower_pid_all_in_layer1 (R : Type*) [CommRing R]
    (hnoether : ∀ I : Ideal R, I.IsFinitelyGenerated)
    (hpid : ∀ I : Ideal R, ∃ r : R, I = Ideal.span {r})
    (I : Ideal R) :
    I ∈ (idealTower R hnoether).layer (1 : ℕ) := by
  obtain ⟨r, hr⟩ := hpid I
  rw [hr]
  exact idealTower_principal_in_layer1 R hnoether r

/-!
## 射の例：準同型が誘導する構造塔の射
-/

/-!
### 部分群階層の射

群準同型 φ : G → G' は、部分群の階層に射を誘導する。

**数学的内容**：
- φ(H) := {φ(h) | h ∈ H}（部分群の像）
- S が H を生成 ⇒ φ(S) が φ(H) を生成
- したがって、生成元の個数は増えない
-/

/-- 準同型が生成元の個数を保存する（以下）補題 -/
lemma Subgroup.map_preserves_generation {G G' : Type*} [Group G] [Group G'] [DecidableEq G']
    (φ : G →* G') (H : Subgroup G) (S : Finset G)
    (hgen : H.IsFinGenBy S) :
    ∃ S' : Finset G', S'.card ≤ S.card ∧ (H.map φ).IsFinGenBy S' := by
  classical
  -- 生成集合として φ(S) を選ぶ
  refine ⟨S.image φ, Finset.card_image_le, ?_⟩
  -- 生成に関する等式を展開
  dsimp [Subgroup.IsFinGenBy] at hgen ⊢
  -- hgen : H = closure (S : Set G)
  have hH : H = Subgroup.closure (S : Set G) := hgen
  have hmap :
      (Subgroup.closure (S : Set G)).map φ =
        Subgroup.closure (φ '' (S : Set G)) :=
    subgroup_map_closure (φ := φ) (s := (S : Set G))
  calc
    H.map φ
        = (Subgroup.closure (S : Set G)).map φ := by simpa [hH]
    _ = Subgroup.closure (φ '' (S : Set G)) := hmap
    _ = Subgroup.closure (S.image φ : Set G') := by
          -- `Finset.coe_image` converts between image of a Finset and Set.image
          simpa [Finset.coe_image]

/-- 準同型がイデアル生成元の個数を保存する補題 -/
lemma Ideal.map_preserves_generation {R R' : Type*} [CommRing R] [CommRing R'] [DecidableEq R']
    (φ : R →+* R') (I : Ideal R) (S : Finset R)
    (hgen : I.IsFinGenBy S) :
    ∃ S' : Finset R', S'.card ≤ S.card ∧ (I.map φ).IsFinGenBy S' := by
  classical
  refine ⟨S.image φ, Finset.card_image_le, ?_⟩
  dsimp [Ideal.IsFinGenBy] at hgen ⊢
  calc
    I.map φ
        = Ideal.span (φ '' (S : Set R)) := by
            -- hgen : I = Ideal.span (S : Set R)
            -- map_span : map φ (span S) = span (φ '' S)
            simpa [hgen, _root_.Ideal.map_span]
    _ = Ideal.span (S.image φ : Set R') := by
            simpa [Finset.coe_image]

/-- 群準同型が誘導する部分群階層の射 -/
def subgroupTowerHom {G G' : Type*} [Group G] [Group G'] [DecidableEq G']
    (hfg : ∀ H : Subgroup G, H.IsFinitelyGenerated)
    (hfg' : ∀ H : Subgroup G', H.IsFinitelyGenerated)
    (φ : G →* G') :
    subgroupTower G hfg ⟶ᴰ subgroupTower G' hfg' where
  map := fun H => H.map φ
  map_layer := by
    intro n
    use n
    intro H' hH'
    -- hH' : H' ∈ φ '' {H | ∃ S, |S| ≤ n ∧ ...}
    obtain ⟨H, ⟨S, hcard, hgen⟩, rfl⟩ := hH'
    -- 補題を適用
    obtain ⟨S', hcard', hgen'⟩ := Subgroup.map_preserves_generation φ H S hgen
    exact ⟨S', le_trans hcard' hcard, hgen'⟩

/-!
### イデアル階層の射

環準同型 φ : R → R' は、イデアルの階層に射を誘導する。

**注意**：一般の環準同型では、像はイデアルにならない可能性がある。
全射準同型の場合に限定するか、または拡大イデアル（extended ideal）を使用する。
-/

/-- 全射準同型が誘導するイデアル階層の射（骨格版） -/
def idealTowerHom {R R' : Type*} [CommRing R] [CommRing R'] [DecidableEq R']
    (hnoether : ∀ I : Ideal R, I.IsFinitelyGenerated)
    (hnoether' : ∀ I : Ideal R', I.IsFinitelyGenerated)
    (φ : R →+* R')
    (_hsurj : Function.Surjective φ) :
    idealTower R hnoether ⟶ᴰ idealTower R' hnoether' where
  map := fun I => I.map φ
  map_layer := by
    intro n
    use n
    intro I' hI'
    rcases hI' with ⟨I, ⟨S, hcard, hgen⟩, rfl⟩
    rcases Ideal.map_preserves_generation (φ := φ) I S hgen with ⟨S', hcard', hgen'⟩
    exact ⟨S', le_trans hcard' hcard, hgen'⟩

/-!
## 具体例：整数環 ℤ

整数環は単項イデアル整域（PID）なので、
すべてのイデアルが1個の元で生成される。
-/

section IntegerExamples

/-- ℤ のすべてのイデアルは有限生成 -/
lemma int_ideals_finitely_generated : ∀ I : Ideal ℤ, I.IsFinitelyGenerated := by
  classical
  intro I
  haveI : I.IsPrincipal := IsPrincipalIdealRing.principal (R := ℤ) (S := I)
  -- 生成元を取り出す（typeclass から）
  let a : ℤ := Submodule.IsPrincipal.generator (S := (I : Ideal ℤ))
  have hspan : Ideal.span ({a} : Set ℤ) = I := by
    simpa [a] using (Ideal.span_singleton_generator (R := ℤ) (I := I))
  have ha : I = Ideal.span ({a} : Set ℤ) := hspan.symm
  refine ⟨{a}, ?_⟩
  simpa [Ideal.IsFinGenBy, ha]

/-- ℤ のイデアル構造塔 -/
def intIdealTower : TowerD :=
  idealTower ℤ int_ideals_finitely_generated

/-- ℤ では、すべての非零イデアルが層1に属する -/
lemma int_nonzero_ideals_in_layer1 (I : Ideal ℤ) (_hI : I ≠ ⊥) :
    I ∈ intIdealTower.layer (1 : ℕ) := by
  classical
  haveI : I.IsPrincipal := IsPrincipalIdealRing.principal (R := ℤ) (S := I)
  let a : ℤ := Submodule.IsPrincipal.generator (S := (I : Ideal ℤ))
  have hspan : Ideal.span ({a} : Set ℤ) = I := by
    simpa [a] using (Ideal.span_singleton_generator (R := ℤ) (I := I))
  have ha : I = Ideal.span ({a} : Set ℤ) := hspan.symm
  refine ⟨{a}, ?_, ?_⟩
  · simp [Finset.card_singleton]
  · simpa [Ideal.IsFinGenBy, ha]

end IntegerExamples

/-!
## まとめ

このファイルでは、Cat_Dの代数的応用として以下を実装しました：

1. **部分群の階層**（`subgroupTower`）
   - 有限生成群の仮定のもとで完全に定義
   - 自明な部分群、巡回部分群の性質

2. **イデアルの階層**（`idealTower`）
   - Noether環の仮定のもとで完全に定義
   - 零イデアル、単項イデアルの性質
   - PID での特殊な性質

3. **射の構成**
   - 群準同型が誘導する部分群階層の射
   - 環準同型が誘導するイデアル階層の射

4. **具体例**
   - 整数環 ℤ のイデアル階層

**Cat_Dの有効性**：
- 生成元の個数という「存在量化的」な条件が自然に扱える
- minLayerの明示的選択が不要
- 準同型による射の構成が自然

**今後の拡張**：
- 他の代数的構造（加群、ベクトル空間）
- 代数的数論への応用（素イデアル分解）
- ホモロジー代数との関連
-/

end ST.TowerD.AlgebraicApplications

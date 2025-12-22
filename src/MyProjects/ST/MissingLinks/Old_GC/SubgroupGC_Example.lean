import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Subsemigroup.Operations
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic
import MyProjects.ST.MissingLinks.GC.GaloisClosureAPI

/-!
# 部分群生成による具体例：ガロア接続の代数的応用

このファイルは、GaloisClosureAPI を代数的構造（群の部分群）に適用し、
線形包とは異なる文脈でガロア接続が同様に機能することを示す。

## 数学的設定

基礎集合：ℤ （整数の加法群）
部分構造：ℤ の部分群（Additive Subgroups）

ガロア接続：
- **Gen(s)** = ⟨s⟩：集合 s が生成する部分群
- **Cl(H)** = H.carrier：部分群 H の台集合

ガロア接続の公理：`⟨s⟩ ≤ H ↔ s ⊆ H.carrier`

## 線形包との対比

| 概念          | 線形包（ベクトル空間）        | 部分群生成（群）              |
|---------------|------------------------------|-------------------------------|
| Gen(s)        | span(s)                      | ⟨s⟩（生成される部分群）       |
| 演算          | 線形結合                     | 群演算・逆元                   |
| 層 n          | n個のベクトルで生成          | n個の生成元で生成             |
| minLayer(x)   | 表現に必要な最小基底数        | 表現に必要な最小生成元数       |
| 具体例        | ℚ² の部分空間                | ℤ の部分群                    |

## 教育的価値

この例により、ガロア接続フレームワークが：
1. 線形代数だけでなく代数学全般に適用可能
2. 異なる数学的構造の共通パターンを抽出
3. 構造保存性（準同型）と自然に両立

することが理解できる。
-/

namespace SubgroupGC

open GaloisClosure

/-! ## Part 1: 部分群のガロア接続インスタンス -/

section SubgroupInstance

variable {G : Type*} [Group G]

/--
**部分群のガロア接続**：群の部分群は自然にガロア接続を成す。

- gen(s) := Subgroup.closure s （集合 s が生成する部分群）
- cl(H) := (H : Set G) （部分群 H の台集合）

ガロア接続の直観：
- 「s から生成される部分群が H に含まれる」
- ⇔「s の各元が H に含まれる」

これは部分群の普遍性（universal property）の圏論的表現。
-/
instance subgroupGC : GeneratorClosureGC G (Subgroup G) where
  gen := Subgroup.closure
  cl := fun H => (H : Set G)
  gc := by
    intro s H
    constructor
    · -- closure s ≤ H → s ⊆ ↑H
      intro h x hx
      exact h (Subgroup.subset_closure hx)
    · -- s ⊆ ↑H → closure s ≤ H
      intro h
      exact (Subgroup.closure_le (K := H)).2 h
  cl_mono := by
    intro H₁ H₂ h
    exact h

/--
部分群生成の拡大性：集合 s は、それが生成する部分群に含まれる。
-/
theorem subgroup_extensive (s : Set G) : s ⊆ ↑(Subgroup.closure s) :=
  subset_cl_gen (S := Subgroup G) s

/--
部分群生成の単調性：s ⊆ t ならば ⟨s⟩ ≤ ⟨t⟩
-/
theorem subgroup_monotone {s t : Set G} (h : s ⊆ t) :
    Subgroup.closure s ≤ Subgroup.closure t :=
  gen_mono h

/--
部分群生成の冪等性：⟨⟨s⟩⟩ = ⟨s⟩

証明：ガロア接続から導出される cl_cl_eq を適用。
-/
theorem subgroup_idempotent (s : Set G) :
    Subgroup.closure (↑(Subgroup.closure s) : Set G) = Subgroup.closure s := by
  exact Subgroup.closure_eq (K := Subgroup.closure s)

end SubgroupInstance

section AddSubgroupInstance

variable {A : Type*} [AddGroup A]

instance addSubgroupGC : GeneratorClosureGC A (AddSubgroup A) where
  gen := AddSubgroup.closure
  cl := fun H => (H : Set A)
  gc := by
    intro s H
    constructor
    · intro h x hx
      exact h (AddSubgroup.subset_closure hx)
    · intro h
      exact (AddSubgroup.closure_le (K := H)).2 h
  cl_mono := by
    intro H₁ H₂ h
    exact h

end AddSubgroupInstance

/-! ## Part 2: ℤ の具体例 -/

section IntExample

-- Additive group ℤ. Lean already provides an AddGroup instance for Int.

/--
**ℤ の部分群の特徴づけ**：
ℤ の部分群は常に nℤ = {nk | k ∈ ℤ} の形（主イデアル）

補題：
- ⟨∅⟩ = {0} = 0ℤ
- ⟨{n}⟩ = nℤ
- ⟨{m, n}⟩ = gcd(m,n)ℤ
-/

-- 単一元から生成される部分群：⟨{n}⟩ = nℤ
theorem closure_singleton_int (n : ℤ) :
    AddSubgroup.closure ({n} : Set ℤ) = AddSubgroup.zmultiples n := by
  ext k
  simp [AddSubgroup.mem_closure_singleton, AddSubgroup.mem_zmultiples_iff]

/--
**生成元数による層の記述**：

- 層 0：⟨∅⟩ = {0}
- 層 1：⟨{n}⟩ = nℤ（1個の元で生成される部分群）
- 層 2：⟨{m, n}⟩ = gcd(m,n)ℤ（2個の元で生成される部分群）

重要な観察：ℤ は巡回群なので、層 1 で ℤ 全体を生成できる（⟨{1}⟩ = ℤ）
-/

-- 層 0：空集合から生成される部分群は自明な部分群 {0}
theorem genCountLayer_zero_int :
    genCountLayer (α := ℤ) (S := AddSubgroup ℤ) 0 = {0} := by
  ext k
  constructor
  · intro ⟨s, hs_card, hk⟩
    -- s.card ≤ 0 より s = ∅
    have hs : s = ∅ := by
      apply Finset.card_eq_zero.mp
      exact Nat.eq_zero_of_le_zero hs_card
    subst hs
    have hk' : k = 0 := by
      simpa [gen, cl, AddSubgroup.closure_empty] using hk
    subst hk'
    rfl
  · intro hk
    subst hk
    refine ⟨∅, by simp, ?_⟩
    dsimp [gen, cl]
    exact AddSubgroup.zero_mem _

/--
層 1：1個の元で生成される部分群に含まれる元

ℤ は巡回群なので、⟨{1}⟩ = ℤ より、層 1 = ℤ 全体
-/
theorem genCountLayer_one_int :
    genCountLayer (α := ℤ) (S := AddSubgroup ℤ) 1 = Set.univ := by
  ext k
  constructor
  · intro _; trivial
  · intro _
    -- k ∈ ⟨{k}⟩ を示す（自明）
    refine ⟨{k}, ?_, ?_⟩
    · -- {k}.ncard ≤ 1
      simp
    · -- k ∈ closure {k}
      have hk' : k ∈ (({k} : Finset ℤ) : Set ℤ) := by
        simp
      exact AddSubgroup.subset_closure hk'

/-!
### minLayer の具体的計算

ℤ において：
- minLayer(0) = 0（生成元不要）
- minLayer(n) = 1（n ≠ 0 なら {n} で生成可能）

これは線形包の場合と異なり、層 1 で全体を覆える。
-/

/--
**ℤ の minLayer 関数**：
- 0 → 0
- n ≠ 0 → 1
-/
noncomputable def minLayerInt (n : ℤ) : ℕ :=
  if n = 0 then 0 else 1

/--
minLayerInt が実際に構造塔の minLayer と一致することの検証。
-/
theorem minLayer_eq_minLayerInt :
    ∀ n : ℤ, (structureTowerFromGC (fun k => ⟨1, by rw [genCountLayer_one_int]; trivial⟩)).minLayer n =
      minLayerInt n := by
  sorry  -- 完全な証明には層の精密な特徴づけが必要

end IntExample

/-! ## Part 3: 有限生成部分群の理論 -/

section FinitelyGenerated

variable {G : Type*} [Group G]

/--
**有限生成部分群**：有限個の元で生成される部分群。

定義：H が有限生成 ⇔ ∃ s : Set G, s.Finite ∧ H = ⟨s⟩
-/
def IsFinitelyGenerated (H : Subgroup G) : Prop :=
  ∃ s : Set G, s.Finite ∧ H = Subgroup.closure s

/--
有限生成性は層の被覆性と密接に関係する。

直観：
- H が有限生成 ⇔ H の全ての元が有限個の生成元で表現可能
- これは genCountLayer の被覆性そのもの
-/
theorem finitely_generated_iff_covered (H : Subgroup G) :
    IsFinitelyGenerated H ↔
    ∃ n : ℕ, ∀ x ∈ H, x ∈ genCountLayer (S := Subgroup G) n := by
  sorry  -- 証明のスケッチ：有限生成 ⇔ 有限個の層で被覆

/--
**ℤ の全ての部分群は有限生成**（実際には1個の元で生成）

これは整数論の基本定理の一つ。
-/
theorem int_subgroups_finitely_generated (H : Subgroup (Multiplicative ℤ)) :
    IsFinitelyGenerated H := by
  -- ℤ は主イデアル整域なので、任意の部分群は1個の元で生成される
  sorry  -- Mathlib の zmultiples 関連の補題を使う

end FinitelyGenerated

/-! ## Part 4: 準同型と構造保存性 -/

section Homomorphisms

variable {G H : Type*} [Group G] [Group H]

/--
**準同型は構造塔の射を誘導する**

群準同型 f : G →* H は、部分群の包含関係を保存するので、
自然に構造塔の射になる。

直観：
- f(⟨s⟩_G) ⊆ ⟨f(s)⟩_H
- これは「生成を保存する」ことを意味する
-/
theorem homomorphism_preserves_generation (f : G →* H) (s : Set G) :
    f '' ↑(Subgroup.closure s) ⊆ ↑(Subgroup.closure (f '' s)) := by
  intro y hy
  rcases hy with ⟨x, hx, hy⟩
  subst hy
  have hx_map : f x ∈ (Subgroup.closure s).map f :=
    Subgroup.mem_map_of_mem f hx
  simpa [MonoidHom.map_closure] using hx_map

/--
全射準同型は minLayer を減らさない（または保つ）

直観：surjective f なら、H の元を表現するのに必要な生成元数は
G の対応する元の生成元数以下。
-/
theorem surjective_hom_preserves_minLayer (f : G →* H) (hf : Function.Surjective f) :
    ∀ y : H, ∃ x : G, f x = y ∧
      (structureTowerFromGC (α := H) (S := Subgroup H) sorry).minLayer y ≤
        (structureTowerFromGC (α := G) (S := Subgroup G) sorry).minLayer x := by
  sorry  -- 完全な証明には被覆性の仮定が必要

end Homomorphisms

/-! ## Part 5: 教育的まとめ -/

section EducationalComparison

/-!
### 線形包 vs 部分群生成：共通点と相違点

#### 共通点（ガロア接続フレームワークが捉えるもの）

1. **生成と閉包の双対性**
   - 両方とも Gen(s) ≤ t ↔ s ⊆ Cl(t) を満たす
   - 単調性、拡大性、冪等性が自動的に従う

2. **階層構造**
   - genCountLayer による層分け
   - minLayer = 最小生成元数

3. **射の定義**
   - 線形写像（ベクトル空間）/ 準同型（群）
   - どちらも生成を保存する

#### 相違点（具体的構造が異なる部分）

1. **層の分布**
   - ℚ²：層 0 = {0}, 層 1 = 軸, 層 2 = 全体
   - ℤ：層 0 = {0}, 層 1 = 全体（巡回群の性質）

2. **演算の性質**
   - 線形包：線形結合（連続的）
   - 部分群：群演算（離散的）

3. **次元 vs 階数**
   - ベクトル空間：次元理論
   - 群：ランク理論（有限生成アーベル群）

### フレームワークの威力

ガロア接続という抽象概念を共有することで：
- 異なる分野の定理が統一的に理解できる
- 一方で証明した定理が他方でも適用可能
- 新しい数学的構造への拡張が容易

### 次の応用例

1. **環のイデアル生成**
   - Gen(s) = 元の集合 s が生成するイデアル
   - 可換環論への応用

2. **位相的閉包**
   - Gen(s) = s を含む最小の閉集合
   - 位相空間論への応用

3. **グラフの到達可能性**
   - Gen(s) = 頂点集合 s から到達可能な頂点
   - 組合せ論への応用
-/

end EducationalComparison

end SubgroupGC

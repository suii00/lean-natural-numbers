import MyProjects.ST.CAT.Cat_D
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Real.Archimedean

/-!
# Cat_Dの具体例と応用

このファイルは構造塔の圏Cat_Dの具体例と応用を提供します。

## なぜCat_Dか？

Cat_Dは以下の特徴により、柔軟な応用が可能です：
- **射はmapのみ**：indexMapの明示的構成が不要
- **存在量化による層保存**：∀i, ∃j, map(layer i) ⊆ layer' j
- **minLayerなし**：より広いクラスの構造を扱える

これにより、確率論の可測写像、フィルトレーション理論、
代数構造の階層など、多様な応用が自然に記述できます。

## 主な内容

1. **基本的な具体例**
   - 実数区間の構造塔（realIntervalTower）
   - 有限集合の冪集合構造塔（finsetPowerTower）

2. **確率論への応用**
   - σ-代数フィルトレーション（simpleFiltrationTower）
   - 離散時間の情報構造

3. **代数的構造**
   - 部分群の階層（sketched）
   - イデアル生成（sketched）

4. **射の構成例**
   - 区間の伸縮写像
   - 冪集合の単調写像
   - フィルトレーション間の可測写像

## 参考文献
- Cat_D.lean：基本定義
- Bourbaki_Lean_Guide.lean：natInitialSegmentsの実装パターン
- SigmaAlgebraTower.md：確率論への応用
-/

namespace ST.TowerD.Examples

open Set

/-!
### 例1：実数区間の構造塔

実数の区間 [0, n] を層とする構造塔。
これは連続的な階層構造の離散近似として機能します。

**数学的意味**：
- layer n = [0, n] = {x : ℝ | 0 ≤ x ≤ n}
- 各実数xは、x ≤ n を満たす最小のn（の上限）に属する
- Cat_Dでは、minLayerを明示的に選ぶ必要がない

**応用**：
- 連続時間の離散化
- 成長過程のモデル化
- 時間発展の階層構造
-/

/-- 実数区間の構造塔

層 n は区間 [0, n] として定義される。
すべての非負実数はいずれかの層に属する（被覆性）。
n ≤ m ならば [0, n] ⊆ [0, m]（単調性）。
-/
def realIntervalTower : TowerD where
  carrier := ℝ
  Index := ℝ
  indexPreorder := (inferInstance : Preorder ℝ)

  layer n := {x : ℝ | x ≤ n}

  covering := by
    intro x
    refine ⟨x, ?_⟩
    simp

  monotone := by
    intro i j hij x hx
    exact le_trans hx hij

/-!
### 例2：有限集合の冪集合構造塔（改善版）

濃度による階層化をより明確に定義します。
-/

open ST  -- TowerD が ST 名前空間なら

/-- 有限集合の冪集合構造塔

Fin n の部分集合を濃度で階層化する。
layer k = {S : Finset (Fin n) | S.card ≤ k}
-/
def finsetPowerTower (n : ℕ) : TowerD where
  carrier := Finset (Fin n)
  Index   := ℕ
  indexPreorder := inferInstance

  -- 各層：濃度が k 以下の部分集合
  layer (k : ℕ) := {S : Finset (Fin n) | S.card ≤ k}

  -- 被覆性
  covering := by
    intro S
    refine ⟨S.card, ?_⟩
    exact (le_rfl : S.card ≤ S.card)

  -- 単調性
  monotone := by
    intro i j hij S hS
    exact le_trans hS hij



/-- 空集合は層0に属する -/
lemma finsetPowerTower_empty_in_layer0 (n : ℕ) :
    (∅ : Finset (Fin n)) ∈ (finsetPowerTower n).layer (0 : ℕ) := by
  -- ゴール:
  --   ∅ ∈ {S : Finset (Fin n) | S.card ≤ 0}
  -- に展開されるので、S.card = 0 を使って終わる
  simp [finsetPowerTower]


/-- 全体集合は層nに属する -/
lemma finsetPowerTower_univ_in_layerN (n : ℕ) :
    Finset.univ ∈ (finsetPowerTower n).layer n := by
  simp [finsetPowerTower, Finset.card_univ, Fintype.card_fin]

/-- 単集合は層1に属する -/
lemma finsetPowerTower_singleton_in_layer1 {n : ℕ} (i : Fin n) :
    ({i} : Finset (Fin n)) ∈ (finsetPowerTower n).layer (1 : ℕ) := by
  -- ゴール:
  --   ({i}.card ≤ 1)
  -- に展開され、`card_singleton` で 1 に簡約される
  simp [finsetPowerTower, Finset.card_singleton]



/-!
### 射の例2：冪集合間の部分集合制限（完全版）
-/

/-- 小さい有限集合への制限写像 -/
def finsetRestrict {n m : ℕ} (h : n ≤ m)
    (S : Finset (Fin m)) : Finset (Fin n) :=
  -- まず値が n 未満のものだけを残し、`Fin.castLT` で型を落とす
  (S.filter (fun i : Fin m => i.1 < n)).attach.image
    (fun i =>
      let hlt : i.1.val < n := (Finset.mem_filter.1 i.2).2
      Fin.castLT i.1 hlt)

/-- 制限写像が層の濃度を保存する補題 -/
lemma finsetRestrict_card_le {n m : ℕ} (h : n ≤ m) (S : Finset (Fin m)) :
    (finsetRestrict h S).card ≤ S.card := by
  classical
  unfold finsetRestrict
  -- filter → attach → image なので要素数は元以下
  have hfilter : ((S.filter fun i : Fin m => i.1 < n).attach).card
      = (S.filter fun i : Fin m => i.1 < n).card := by simp
  have hfilter_le : (S.filter fun i : Fin m => i.1 < n).card ≤ S.card :=
    Finset.card_filter_le _ _
  calc
    (Finset.card
        ((S.filter fun i : Fin m => i.1 < n).attach.image
          (fun i =>
            let hlt : i.1.val < n := (Finset.mem_filter.1 i.2).2
            Fin.castLT i.1 hlt))) ≤
        (S.filter fun i : Fin m => i.1 < n).attach.card := by
          exact Finset.card_image_le
    _ = (S.filter fun i : Fin m => i.1 < n).card := by simpa [hfilter]
    _ ≤ S.card := hfilter_le

/-- 制限写像が誘導する構造塔の射 -/
def finsetPowerRestrict {n m : ℕ} (h : n ≤ m) :
    finsetPowerTower m ⟶ᴰ finsetPowerTower n where
  map := finsetRestrict h
  map_layer := by
    intro k
    refine ⟨k, ?_⟩
    intro T hT
    have hcard := finsetRestrict_card_le h T
    exact le_trans hcard hT

/-!
### 実数区間の射：平行移動
-/

/-- 実数の平行移動 -/
def realShiftMap (c : ℝ) : ℝ → ℝ := fun x => x + c

/-- 平行移動が誘導する構造塔の射 -/
def realIntervalShift (c : ℝ) :
    realIntervalTower ⟶ᴰ realIntervalTower where
  map := realShiftMap c
  map_layer := by
    intro n
    refine ⟨n + Real.abs c, ?_⟩
    intro y ⟨x, hx, rfl⟩
    have : x + c ≤ x + Real.abs c := by nlinarith [abs_nonneg c]
    have hx' : x ≤ n := hx
    nlinarith

/-!
### 例3：簡易フィルトレーション構造塔

σ-代数の増大列をCat_Dの構造塔として表現します。

**確率論的解釈**：
- carrier = Set Ω（標本空間の部分集合族）
- layer n = F_n（時刻nまでに観測可能な事象）
- 単調性：F_n ⊆ F_{n+1}（情報の単調増加）

**Cat_Dが適切な理由**：
- フィルトレーション間の可測写像は、各層を「どこかの層」に写せば十分
- minLayerの明示的構成は不要（事象が初めて可測になる時刻は非自明）
- 存在量化の層保存条件が、可測性の自然な条件に対応

この例は簡易版です。完全な実装はSigmaAlgebraTower.mdを参照。
-/

/-- 簡易フィルトレーション構造塔

各時刻で観測可能な事象の集合を層とする。
ここでは具体的な可測空間の構造は省略し、
抽象的な集合の増大列として定義する。
-/
structure SimpleFiltration (Ω : Type*) where
  /-- 各時刻で観測可能な事象の集合 -/
  events : ℕ → Set (Set Ω)
  /-- 単調性：時間が進むと観測可能な事象が増える -/
  events_mono : ∀ {n m}, n ≤ m → events n ⊆ events m

/-- 簡易フィルトレーションから構造塔を構成

`hcover` は「すべての事象がいつかは観測可能になる」という仮定。 -/
def simpleFiltrationTower (Ω : Type*) (F : SimpleFiltration Ω)
    (hcover : ∀ A : Set Ω, ∃ n, A ∈ F.events n) : TowerD where
  carrier := Set Ω
  Index := ℕ
  indexPreorder := (inferInstance : Preorder ℕ)

  layer n := F.events n

  covering := hcover

  monotone := F.events_mono

/-!
## 射の構成例

Cat_Dの射は (map, map_layer) の対であり、
map_layer は存在量化による層保存を要求します。
-/

/-!
### 射の例1：実数区間の伸縮

スケール変換 x ↦ c·x は、適切な indexMap により
構造塔の射を誘導します。
-/

/-- 実数のスケール変換（正の定数倍） -/
def realScaleMap (c : ℝ) (_hc : 0 < c) : ℝ → ℝ := fun x => c * x

/-- スケール変換が誘導する構造塔の射

c > 1 の場合、layer n は layer ⌈c·n⌉ に写される。
-/
def realIntervalScale (c : ℝ) (_hc : 0 < c) :
    realIntervalTower ⟶ᴰ realIntervalTower :=
  -- 簡易版: 恒等射として与える（射の例示が目的）
  HomD.id _

/-!
### 射の例3：フィルトレーション間の可測写像

確率空間の射は、フィルトレーション間の射を誘導します。
-/

/-- フィルトレーション間の射（骨格版）

可測写像 f: Ω → Ω' が各層の事象を「どこかの層」に送ると仮定する。
-/
def filtrationHomD {Ω Ω' : Type*}
    (F : SimpleFiltration Ω) (F' : SimpleFiltration Ω')
    (f : Ω → Ω')
    (h_image_uniform :
      ∀ n, ∃ m, ∀ A, A ∈ F.events n → f '' A ∈ F'.events m)
    (hcov : ∀ A : Set Ω, ∃ n, A ∈ F.events n)
    (hcov' : ∀ A : Set Ω', ∃ n, A ∈ F'.events n) :
    simpleFiltrationTower Ω F hcov ⟶ᴰ simpleFiltrationTower Ω' F' hcov' where
  map := fun A => f '' A
  map_layer := by
    intro n
    obtain ⟨m, hm⟩ := h_image_uniform n
    refine ⟨m, ?_⟩
    intro A hA
    rcases hA with ⟨B, hB, rfl⟩
    exact hm B hB

/-!
## 補助的な性質と補題
-/

/-!
### 実数区間構造塔の性質
-/

/-- 層の特徴付け -/
lemma realIntervalTower_mem_layer (x n : ℝ) :
    x ∈ (realIntervalTower.layer n) ↔ x ≤ n := by
  rfl

/-- 層の包含関係 -/
lemma realIntervalTower_layer_subset {n m : ℝ} (h : n ≤ m) :
    realIntervalTower.layer n ⊆ realIntervalTower.layer m := by
  exact realIntervalTower.monotone h

/-!
## 代数的応用の骨格

以下は、部分群や環のイデアルなど、
代数的構造への応用の骨格です。
完全な実装は別ファイルで提供されます。
-/

section AlgebraicApplications

/-!
### 部分群の階層（スケッチ）

群 G の部分群を、生成元の個数で階層化する。
-/

-- structure SubgroupTower (G : Type*) [Group G] : TowerD where
--   carrier := Subgroup G
--   Index := ℕ
--   layer n := {H : Subgroup G | ∃ S : Finset G, S.card ≤ n ∧ H = Subgroup.closure (S : Set G)}
--   covering := sorry  -- すべての部分群は有限生成と仮定
--   monotone := sorry  -- n ≤ m ⇒ n個で生成可能 ⇒ m個で生成可能

/-!
### 環のイデアル階層（スケッチ）

環 R のイデアルを、生成元の個数で階層化する。
-/

-- structure IdealTower (R : Type*) [CommRing R] : TowerD where
--   carrier := Ideal R
--   Index := ℕ
--   layer n := {I : Ideal R | ∃ S : Finset R, S.card ≤ n ∧ I = Ideal.span (S : Set R)}
--   covering := sorry  -- Noether環の場合は成立
--   monotone := sorry

end AlgebraicApplications

/-!
## 位相的応用の骨格

開集合の階層、閉包演算の反復など、
位相空間論への応用の骨格です。
-/

section TopologicalApplications

/-!
### 開集合の階層（スケッチ）

位相空間 X の開集合を、基本開集合の和の個数で階層化する。
-/

-- structure OpenSetTower (X : Type*) [TopologicalSpace X] : TowerD where
--   carrier := {U : Set X // IsOpen U}
--   Index := ℕ
--   layer n := {⟨U, hU⟩ | ∃ (S : Finset (Set X)),
--                S.card ≤ n ∧ (∀ V ∈ S, IsOpen V) ∧ U = ⋃₀ (S : Set (Set X))}
--   covering := sorry  -- 第二可算公理を持つ場合は成立
--   monotone := sorry

end TopologicalApplications

/-!
## まとめ

このファイルでは、Cat_Dの柔軟性を活かして、
様々な数学的構造を統一的に扱う例を示しました。

**Cat_Dの利点**：
1. minLayerの明示的構成が不要
   → より広いクラスの構造を自然に扱える

2. 存在量化による層保存
   → 確率論の可測性、代数の生成など、
     「どこかで成立すればよい」条件に対応

3. 射の合成が自動的に閉じる
   → 複雑な構造の合成が容易

**今後の展開**：
- 各応用の完全な実装（別ファイル）
- 圏論的性質の詳細な証明
- 具体的な定理の形式化
-/

end ST.TowerD.Examples

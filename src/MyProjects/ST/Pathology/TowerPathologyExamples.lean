import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic

/-!
# Structure Tower Pathology Examples

このファイルは StructureTowerWithMin と rank/minLayer の対応に関する
**病的・境界・反例** の具体例を集めたものである。

## 設計意図

正常な例（canonical examples）だけでなく、公理のどれか一つが壊れる例や、
ほぼ公理を満たすが微妙に失敗する例を示し、理論の限界と公理の必要性を明確化する。

## ラベル体系

- **trivial**: 最小・自明な例（単点、空塔など）
- **canonical**: 正規形としての標準的な例
- **extreme**: 添字集合や carrier が極端に大きい・複雑
- **pathological**: 公理の一つを意図的に壊した例
- **counterexample**: ある定理の逆が成り立たないことを示す
- **dual**: 順序を反転した双対構成
- **borderline (tight)**: 公理をギリギリ満たす境界例
- **non-example (almost-example)**: あと一歩で公理を満たすが失敗
- **out-of-category (meta)**: 圏論的に塔ではないが塔風の構造
- **schema (template)**: パラメータ化された例のテンプレート
- **finite computational**: 有限で完全に計算可能な例

## Contents

1. 例カタログ（コメント形式）
2. Lean で実装した pathological / non-example 2例

## 例カタログ（20個）

### Trivial (2個)

1. **pointTower**: carrier = Unit, Index = ℕ, layer n = {()}, minLayer () = 0
   - 最も自明。すべての公理が trivially satisfied。

2. **emptyIndexTower**: carrier = ℕ, Index = Fin 0（空）
   - covering が vacuously true だが意味のある塔にならない。
   - 実際には StructureTowerWithMin として構成不可（Fin 0 に対し covering が空）。

### Canonical (2個)

3. **natIdentityTower**: carrier = ℕ, layer n = {k | k ≤ n}, minLayer = id
   - rank ≡ minLayer の正規形。RankTower.lean の標準例。

4. **intAbsTower**: carrier = ℤ, layer n = {k | |k| ≤ n}, minLayer = |·|
   - DecidableStructureTower_Examples.lean の標準例。

### Extreme (2個)

5. **productTower**: carrier = ℕ × ℕ, Index = ℕ × ℕ,
   layer (i, j) = {(a, b) | a ≤ i ∧ b ≤ j}, minLayer = id
   - 2次元添字。積塔の標準構成。

6. **infiniteWidthTower**: carrier = ℕ → ℕ（関数空間）, Index = ℕ,
   layer n = {f | ∀ k ≤ n, f k ≤ n}
   - carrier が非可算だが添字は可算。

### Pathological (2個)

7. **nonMonotoneTower** [★実装]: carrier = ℕ, Index = ℕ,
   layer n = if n = 1 then ∅ else {k | k ≤ n}
   - monotonicity が壊れる（layer 1 ⊄ layer 2 ではない）。

8. **nonCoveringTower** [★実装]: carrier = ℕ, Index = ℕ,
   layer n = {k | k ≤ n ∧ k ≠ 0}
   - covering が壊れる（0 はどの層にも属さない）。

### Counterexample (2個)

9. **rankNotUniqueTower**: carrier = ℕ, Index = ℕ × ℕ（非線形順序）,
   layer (i, j) = {k | k ≤ i ∨ k ≤ j}
   - minLayer が一意に定まらない（最小元が存在しない）。
   - 線形順序でないと正規の rank が得られない反例。

10. **layerNotSetTower**: 層を部分集合でなく述語としてもつ「前段階」構造
    - Set X ではなく X → Prop として層を与える。
    - StructureTowerWithMin として形式化するには Set に変換が必要。

### Dual (2個)

11. **codepthTower**: carrier = ℕ, Index = ℕᵒᵈ（OrderDual）,
    layer n = {k | n ≤ k}, minLayer = id
    - depth の双対として「上からの層」を考える。

12. **topologyRefinementTower**: carrier = Set X, Index = TopologicalSpace Xᵒᵈ
    - より細かい位相が「小さい」となる双対順序。

### Borderline / Tight (2個)

13. **singletonLayerTower**: carrier = ℕ, layer n = {n}, minLayer = id
    - 各層が singleton。monotonicity は n ≤ m で {n} ⊆ {m} を要求…失敗！
    - 実際には non-example だが、「境界」として見える。

14. **thresholdTower**: carrier = ℕ, layer n = if n ≥ 10 then ℕ else {k | k ≤ n}
    - n < 10 まで標準、n ≥ 10 で全体。covering は OK、monotone も OK。

### Non-example / Almost-example (2個)

15. **partialMinLayer**: covering と monotone は成立、minLayer が部分関数
    - 一部の x で最小層が定義されない。
    - Lean で Option ℕ を返す形で表現可能だが、構造としては不完全。

16. **multiMinimalTower**: carrier = ℕ, Index = Finset ℕ（部分集合束）
    - 各 x に対し x ∈ layer S となる S が複数の極小を持つ。
    - well-defined な minLayer がない（一意でない）。

### Out-of-category / Meta (2個)

17. **preSheafTower**: carrier が圏 C の関手 F : Cᵒᵖ → Set
    - 層ではなく前層として「塔的」な構造を考える。
    - StructureTowerWithMin には直接収まらない。

18. **gradedModuleTower**: 次数付き加群として塔を見る視点
    - carrier が加群、layer が次数成分の和。
    - StructureTowerWithMin の additive 版として構造化可能。

### Schema / Template (2個)

19. **closureOperatorTower T**: 閉包演算子 c から塔を作るテンプレート
    - layer n = {x | rank_c x ≤ n} where rank_c = closure depth。
    - GaloisConnection から自動生成。

20. **generatedTower S (step : Set X → Set X)**: S から始めて step を繰り返す
    - layer 0 = S, layer (n+1) = step (layer n)
    - Bourbaki の「生成される構造」の一般化。

### Finite Computational (bonus)

21. **fin5Tower**: carrier = Fin 5, layer n = {k | k.val ≤ n}, minLayer k = k.val
    - 完全に計算可能で #eval でテスト可能。
-/

namespace Pathology

open Set

/-!
## 実装 1: NonMonotoneTower

monotonicity 公理が壊れる例。layer 1 = ∅ としつつ layer 2 = {0, 1, 2}。
layer 0 ⊆ layer 1 は {0} ⊆ ∅ となり失敗。
-/

/-- 非単調な「塔もどき」の層定義 -/
def nonMonotoneLayer (n : ℕ) : Set ℕ :=
  if n = 1 then ∅ else {k | k ≤ n}

/-- layer 0 が非空であることを示す -/
example : (0 : ℕ) ∈ nonMonotoneLayer 0 := by
  simp [nonMonotoneLayer]

/-- layer 1 が空であることを示す -/
example : nonMonotoneLayer 1 = ∅ := by
  simp [nonMonotoneLayer]

/-- layer 2 に 0 が属することを示す -/
example : (0 : ℕ) ∈ nonMonotoneLayer 2 := by
  simp [nonMonotoneLayer]

/-- 単調性が壊れていることの証明：
    0 ≤ 1 だが layer 0 ⊄ layer 1 -/
theorem nonMonotoneLayer_fails_monotone :
    ¬ (∀ {i j : ℕ}, i ≤ j → nonMonotoneLayer i ⊆ nonMonotoneLayer j) := by
  intro h
  have h01 : nonMonotoneLayer 0 ⊆ nonMonotoneLayer 1 := h (Nat.zero_le 1)
  have h0_in_layer0 : (0 : ℕ) ∈ nonMonotoneLayer 0 := by simp [nonMonotoneLayer]
  have h0_in_layer1 : (0 : ℕ) ∈ nonMonotoneLayer 1 := h01 h0_in_layer0
  simp [nonMonotoneLayer] at h0_in_layer1

/-!
## 実装 2: NonCoveringTower

covering 公理が壊れる例。layer n = {k | k ≤ n ∧ k ≠ 0}。
この場合、0 はどの層にも属さない。
-/

/-- 0 を含まない「塔もどき」の層定義 -/
def noCoveringLayer (n : ℕ) : Set ℕ :=
  {k | k ≤ n ∧ k ≠ 0}

/-- layer 0 が空であることを示す -/
example : noCoveringLayer 0 = ∅ := by
  ext k
  simp_all [noCoveringLayer]



/-- 0 がどの層にも属さないことを示す -/
theorem zero_not_in_any_noCoveringLayer :
    ∀ n : ℕ, (0 : ℕ) ∉ noCoveringLayer n := by
  intro n
  simp [noCoveringLayer]

/-- covering 公理が壊れていることの証明 -/
theorem noCoveringLayer_fails_covering :
    ¬ (∀ x : ℕ, ∃ i : ℕ, x ∈ noCoveringLayer i) := by
  push_neg
  refine ⟨0, ?_⟩
  intro i
  exact zero_not_in_any_noCoveringLayer i

/-- 単調性は成立することを確認 -/
theorem noCoveringLayer_monotone :
    ∀ {i j : ℕ}, i ≤ j → noCoveringLayer i ⊆ noCoveringLayer j := by
  intro i j hij x hx
  simp [noCoveringLayer] at hx ⊢
  exact ⟨le_trans hx.1 hij, hx.2⟩

/-!
## 補足: 正常な塔（Canonical）の例

比較用に、公理をすべて満たす正常な塔を定義。
-/

/-- 正常な自然数塔（canonical example） -/
def natTowerLayer (n : ℕ) : Set ℕ := {k | k ≤ n}

/-- 被覆性 -/
theorem natTowerLayer_covering : ∀ x : ℕ, ∃ i : ℕ, x ∈ natTowerLayer i := by
  intro x
  exact ⟨x, le_refl x⟩

/-- 単調性 -/
theorem natTowerLayer_monotone :
    ∀ {i j : ℕ}, i ≤ j → natTowerLayer i ⊆ natTowerLayer j := by
  intro i j hij x hx
  exact le_trans hx hij

/-- minLayer = id による正規形 -/
def natTowerMinLayer : ℕ → ℕ := id

/-- minLayer が層に属する -/
theorem natTowerMinLayer_mem : ∀ x : ℕ, x ∈ natTowerLayer (natTowerMinLayer x) := by
  intro x
  simp [natTowerLayer, natTowerMinLayer]

/-- minLayer の最小性 -/
theorem natTowerMinLayer_minimal :
    ∀ x i : ℕ, x ∈ natTowerLayer i → natTowerMinLayer x ≤ i := by
  intro x i hi
  simp [natTowerLayer, natTowerMinLayer] at *
  exact hi

/-!
## 計算可能な例: Fin 5 Tower
-/

/-- Fin 5 の層 -/
def fin5Layer (n : ℕ) : Set (Fin 5) := {k | k.val ≤ n}

/-- Fin 5 の minLayer -/
def fin5MinLayer (k : Fin 5) : ℕ := k.val

/-- 層所属の決定可能性 -/
instance (k : Fin 5) (n : ℕ) : Decidable (k ∈ fin5Layer n) :=
  decidable_of_iff (k.val ≤ n) (by simp [fin5Layer])

/- minLayer の計算テスト -/
#eval fin5MinLayer ⟨0, by omega⟩  -- 0
#eval fin5MinLayer ⟨3, by omega⟩  -- 3
#eval fin5MinLayer ⟨4, by omega⟩  -- 4

/- 層所属のテスト -/
#eval decide ((⟨2, by omega⟩ : Fin 5) ∈ fin5Layer 3)   -- true
#eval decide ((⟨4, by omega⟩ : Fin 5) ∈ fin5Layer 3)   -- false
#eval decide ((⟨4, by omega⟩ : Fin 5) ∈ fin5Layer 4)   -- true

end Pathology

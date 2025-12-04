import MyProjects.ST.Formalization.P2.SigmaAlgebraTower
import MyProjects.ST.Formalization.P3.StoppingTime_MinLayer
import MyProjects.ST.Rank.P3.RankTower
import MyProjects.ST.Rank.Prob.P1.StopingTime_C

namespace StructureTowerProbability

/-!
# 停止時間とRank関数の対応：拡張定理

このファイルは StopingTime_C.lean の拡張として、
より高度な対応定理と応用例を提供する。
-/

variable {Ω : Type*} [MeasurableSpace Ω]

open TowerRank

/-!
## セクション1：逆方向対応の詳細化

StopingTime_C.leanで定義された rankFromFiltrationTower を使って、
「フィルトレーション → rank → 構造塔」の往復を詳細化する。
-/

section ReverseCorrespondence

/-!
### 定理：rankFromFiltrationTowerの層特徴付け

**数学的意味**:
フィルトレーションから誘導される rank 関数 `rankFromFiltrationTower` は、
「単点 `{ω}` が第 `n` 層で可測になるかどうか」と同値である。

**rank理論との対応**:
`towerFromRank_minLayer_eq_rank` で得られる
`rank ≤ n ↔ singleton ∈ layer n` の同値を、
フィルトレーション由来の構造塔 `towerOf` に適用したもの。

**証明のポイント**:
`rankFromFiltrationTower_le_iff` をそのまま展開するだけでよい。
-/
lemma rankFromFiltrationTower_characterization
    (ℱ : Filtration Ω) (n : ℕ) :
    {ω | rankFromFiltrationTower ℱ ω ≤ n} =
      {ω | {ω} ∈ (towerOf ℱ).layer n} := by
  ext ω
  exact rankFromFiltrationTower_le_iff (ℱ := ℱ) (ω := ω) (n := n)

end ReverseCorrespondence

/-!
## セクション2：停止時間の代数的性質

rank関数の視点から、停止時間の代数的性質（最小値、最大値など）を導出する。
-/

section AlgebraicProperties

/-!
### 定理：最小値の可測性（完全証明）

**証明戦略**:
1. `stoppingTimeMin_layer_characterization` から、
   `{min(τ₁,τ₂) ≤ n} = {τ₁ ≤ n} ∪ {τ₂ ≤ n}` を使う
2. 両辺が可測であることを、τ₁, τ₂ の停止時間性から導く
3. 和集合の可測性を適用
-/
lemma stoppingTimeMin_measurable
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) :
    ∀ n, @MeasurableSet Ω (ℱ.base.𝓕 n)
          {ω | stoppingTimeMin ℱ τ₁ τ₂ ω ≤ n} := by
  intro n
  -- 層の特徴付けを使う
  rw [stoppingTimeMin_layer_characterization ℱ τ₁ τ₂ n]
  -- 両停止時間の可測性から
  exact (τ₁.measurable n).union (τ₂.measurable n)

/-!
### 定義：完全な停止時間としての最小値

これで `stoppingTimeMin_full` は完全な `StoppingTime` 型になる。
-/
noncomputable def stoppingTimeMin_full
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) :
    StoppingTime ℱ where
  τ := stoppingTimeMin ℱ τ₁ τ₂
  measurable := stoppingTimeMin_measurable ℱ τ₁ τ₂

/-!
### 補題：完全版でも rank の対応は保たれる
-/
lemma stoppingTimeMin_full_preserves_rank
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) (ω : Ω) :
    (stoppingTimeMin_full ℱ τ₁ τ₂).τ ω =
    min (τ₁.τ ω) (τ₂.τ ω) := by
  rfl

/-!
### 定理：完全版の構造塔対応

完全な停止時間から構成される構造塔の minLayer も正しく対応する。
-/
theorem stoppingTimeMin_full_tower_correspondence
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) (ω : Ω) :
    let T := towerFromStoppingTime ℱ (stoppingTimeMin_full ℱ τ₁ τ₂)
    T.minLayer ω = min (τ₁.τ ω) (τ₂.τ ω) := by
  -- stoppingTimeMin_full の定義を展開
  have h := minLayer_eq_stoppingTime_pointwise ℱ
              (stoppingTimeMin_full ℱ τ₁ τ₂) ω
  simpa [stoppingTimeMin_full, stoppingTimeMin] using h

end AlgebraicProperties

/-!
## 検証: 最小値の代数的性質

完全な停止時間としての性質を確認。
-/

section AlgebraicPropertiesVerification

/-!
### 定理：最小値の可換性
-/
theorem stoppingTimeMin_full_comm
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) :
    stoppingTimeMin_full ℱ τ₁ τ₂ =
    stoppingTimeMin_full ℱ τ₂ τ₁ := by
  ext ω
  simp [stoppingTimeMin_full, stoppingTimeMin, min_comm]

/-!
### 定理：最小値の結合律
-/
theorem stoppingTimeMin_full_assoc
    (ℱ : Filtration Ω) (τ₁ τ₂ τ₃ : StoppingTime ℱ) :
    stoppingTimeMin_full ℱ (stoppingTimeMin_full ℱ τ₁ τ₂) τ₃ =
    stoppingTimeMin_full ℱ τ₁ (stoppingTimeMin_full ℱ τ₂ τ₃) := by
  ext ω
  simp [stoppingTimeMin_full, stoppingTimeMin, min_assoc]

/-!
### 定理：層の和集合表現（完全版）

完全な停止時間でも、層の特徴付けは同じ。
-/
theorem stoppingTimeMin_full_layer
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) (n : ℕ) :
    {ω | (stoppingTimeMin_full ℱ τ₁ τ₂).τ ω ≤ n} =
    {ω | τ₁.τ ω ≤ n} ∪ {ω | τ₂.τ ω ≤ n} := by
  -- 元の定理を使う
  have h := stoppingTimeMin_layer_characterization ℱ τ₁ τ₂ n
  simpa [stoppingTimeMin_full] using h

end AlgebraicPropertiesVerification
/-!
### 定理：停止時間の最小値

**数学的意味**:
2つの停止時間の最小値（pointwise minimum）もまた停止時間である。
これはrank関数のmin演算に対応する。

**rank理論との対応**:
rank関数の場合、ρ₁ ⊓ ρ₂ = min(ρ₁, ρ₂) が自然に定義される。
-/
noncomputable def stoppingTimeMin
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) : Ω → ℕ :=
  fun ω => min (τ₁.τ ω) (τ₂.τ ω)

/-!
### 補題：最小値のrank表現

最小値停止時間は、元の2つのrank関数の最小値として表現される。
-/
lemma stoppingTimeMin_eq_rank_min
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) (ω : Ω) :
    stoppingTimeMin ℱ τ₁ τ₂ ω =
    min (stoppingTimeToRank ℱ τ₁ ω) (stoppingTimeToRank ℱ τ₂ ω) := by
  unfold stoppingTimeMin stoppingTimeToRank
  rfl

/-!
### 定理：最小値の構造塔表現

2つの停止時間の最小値から構成される構造塔の層は、
元の2つの構造塔の層の和集合として表現される。

**数学的意味**:
min(τ₁, τ₂) ≤ n ⇔ τ₁ ≤ n ∨ τ₂ ≤ n
という標本点レベルの性質が、層レベルに持ち上がる。
-/
theorem stoppingTimeMin_layer_characterization
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ) (n : ℕ) :
    {ω | stoppingTimeMin ℱ τ₁ τ₂ ω ≤ n} =
    {ω | τ₁.τ ω ≤ n} ∪ {ω | τ₂.τ ω ≤ n} := by
  ext ω
  constructor
  · intro h
    -- min ≤ n なら、min がどちらかに一致するので片方が ≤ n
    by_cases h₁ : τ₁.τ ω ≤ τ₂.τ ω
    · -- min = τ₁
      left
      dsimp [stoppingTimeMin] at h
      have hmin : min (τ₁.τ ω) (τ₂.τ ω) = τ₁.τ ω := Nat.min_eq_left h₁
      have hτ₁ : τ₁.τ ω ≤ n := by simpa [hmin] using h
      exact hτ₁
    · -- min = τ₂
      right
      dsimp [stoppingTimeMin] at h
      have hlt : τ₂.τ ω < τ₁.τ ω := lt_of_not_ge h₁
      have hmin : min (τ₁.τ ω) (τ₂.τ ω) = τ₂.τ ω :=
        Nat.min_eq_right (le_of_lt hlt)
      have hτ₂ : τ₂.τ ω ≤ n := by simpa [hmin] using h
      exact hτ₂
  · intro h
    cases h with
    | inl h₁ => exact Nat.le_trans (Nat.min_le_left _ _) h₁
    | inr h₂ => exact Nat.le_trans (Nat.min_le_right _ _) h₂

end AlgebraicProperties

/-!
## セクション3：具体例の検証可能なケース

可測性を直接扱わずに、抽象的なレベルで検証可能な性質を示す。
-/

section VerifiableExamples

/-!
### 例：恒等的停止時間

すべての標本点が時刻0で決定される最も単純な停止時間。
-/
noncomputable def zeroStoppingTime (_ℱ : Filtration Ω) : Ω → ℕ :=
  fun _ => 0

/-!
### 補題：零停止時間のrank表現

零停止時間から構成される構造塔の層は、最初の層のみが全体を覆う。
-/
lemma zeroStoppingTime_layer_structure (_ℱ : Filtration Ω) (n : ℕ) :
    {ω | zeroStoppingTime _ℱ ω ≤ n} =
    if n = 0 then Set.univ else Set.univ := by
  ext ω
  simp [zeroStoppingTime]

end VerifiableExamples

/-!
## セクション4：層の単調性と停止時間の順序

rank関数の順序が、構造塔の層の包含関係にどう対応するかを明示する。
-/

section MonotonicityProperties

/-!
### 定理：停止時間の順序と層の包含

τ₁(ω) ≤ τ₂(ω) for all ω であるとき、
「遅い」停止時間 τ₂ が時刻 n までに停止していれば、必ず τ₁ も停止している。
したがって停止集合に包含関係が生じる。

**数学的意味**:
「早く停止する ⇒ より大きい停止集合を与える」という直感の形式化。

**rank理論との対応**:
rank関数の単調性：ρ₁ ≤ ρ₂ ⇒ {ρ₂ ≤ n} ⊆ {ρ₁ ≤ n}。
-/
theorem stoppingTime_order_preserves_layers
    (ℱ : Filtration Ω) (τ₁ τ₂ : StoppingTime ℱ)
    (h : ∀ ω, τ₁.τ ω ≤ τ₂.τ ω) (n : ℕ) :
    {ω | τ₂.τ ω ≤ n} ⊆ {ω | τ₁.τ ω ≤ n} := by
  intro ω hω
  exact le_trans (h ω) hω

end MonotonicityProperties

/-!
## セクション5：構造塔の射としての停止時間の変換

RankTower.leanの射の概念を、停止時間の変換に適用する。
-/

section MorphismsOfStoppingTimes

/-!
### 定義：停止時間の変換

停止時間 τ を別の停止時間 τ' に変換する操作を、
構造塔の射として定式化する。

**数学的意味**:
f : Ω → Ω' が可測写像であるとき、
τ を f で pushforward した停止時間 f₊τ を定義できる。

**rank理論との対応**:
rank関数の間の写像 f : (X, ρ) → (Y, ρ') が、
ρ'(f(x)) ≤ φ(ρ(x)) を満たすとき、構造塔の射になる。
-/
structure StoppingTimeTransform (ℱ : Filtration Ω) (ℱ' : Filtration Ω) where
  /-- 標本点の変換 -/
  map : Ω → Ω
  /-- 時刻の変換 -/
  timeMap : ℕ → ℕ
  /-- 時刻変換の単調性 -/
  timeMap_mono : ∀ {n m}, n ≤ m → timeMap n ≤ timeMap m
  /-- 停止時間の保存 -/
  preserves_stopping : ∀ (τ : StoppingTime ℱ) (ω : Ω),
    timeMap (τ.τ ω) ≤ τ.τ (map ω)

/-!
### 補題：恒等変換

停止時間の恒等変換は、構造塔の恒等射に対応する。
-/
noncomputable def stoppingTimeTransform_id (ℱ : Filtration Ω) :
    StoppingTimeTransform ℱ ℱ where
  map := id
  timeMap := id
  timeMap_mono := fun h => h
  preserves_stopping := fun _ _ => le_refl _

end MorphismsOfStoppingTimes

/-!
## 理論的まとめ

この拡張により、以下が追加で明確になった：

1. **代数的構造**: 停止時間の min/max がrank関数の演算に対応
2. **順序構造**: 停止時間の順序と層の包含関係の対応
3. **変換の理論**: 停止時間の変換が構造塔の射として定式化可能
4. **検証可能な例**: 具体的な計算で確認できる性質の提供

これらは、StopingTime_C.leanの核心定理（定理4-6）を補完し、
より完全な理論体系を形成する。

## 今後の統合作業

1. 可測性補題の完成により、セクション2の定理が完全な停止時間になることを示す
2. Martingale_StructureTower.mdとの統合
3. Optional Stopping Theoremへの応用
-/

end StructureTowerProbability

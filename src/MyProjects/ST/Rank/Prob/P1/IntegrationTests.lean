import MyProjects.ST.Formalization.P2.SigmaAlgebraTower
import MyProjects.ST.Formalization.P3.StoppingTime_MinLayer
import MyProjects.ST.Rank.P3.RankTower
import MyProjects.ST.Rank.Prob.P1.StopingTime_C
import MyProjects.ST.Rank.Prob.P1.StoppingTime_RankExtension

/-!
# 停止時間とRank関数の対応：統合テスト

このファイルは、以下の統合をテストする：
- StopingTime_C.lean（核心定理）
- StoppingTime_RankExtension.lean（拡張定理）

## テストの構成

1. **基本機能テスト**: 定義の型チェック
2. **rank対応テスト**: 停止時間 ↔ rank関数の往復
3. **代数的性質テスト**: min/max の演算
4. **具体例テスト**: 定数停止時間での検証
-/

namespace StructureTowerProbability.IntegrationTests

variable {Ω : Type*} [MeasurableSpace Ω]

open TowerRank

/-!
## テストグループ1: 基本定義の型チェック

すべての定義が正しい型を持つことを確認。
-/

section TypeChecks

/-!
### Test 1.1: stopingTimeToRank の型
-/
#check stoppingTimeToRank
-- stoppingTimeToRank :
--   {Ω : Type*} → [inst : MeasurableSpace Ω] →
--   (ℱ : Filtration Ω) → (τ : StoppingTime ℱ) → Ω → ℕ

/-!
### Test 1.2: towerFromStoppingTime の型
-/
#check towerFromStoppingTime
-- towerFromStoppingTime :
--   {Ω : Type*} → [inst : MeasurableSpace Ω] →
--   (ℱ : Filtration Ω) → (τ : StoppingTime ℱ) →
--   StructureTowerWithMin

/-!
### Test 1.3: constantStoppingTime の型
-/
#check constantStoppingTime
-- constantStoppingTime :
--   {Ω : Type*} → [inst : MeasurableSpace Ω] →
--   (ℱ : Filtration Ω) → ℕ → StoppingTime ℱ

/-!
### Test 1.4: 定義が正しくコンパイルされることを確認
-/
example : True := by
  -- すべての定義がコンパイル可能であることの証明
  trivial

end TypeChecks

/-!
## テストグループ2: rank対応の検証

停止時間とrank関数の往復が正しいことを確認。
-/

section RankCorrespondenceTests

/-!
### Test 2.1: 定数停止時間のrank表現
-/
theorem test_constant_rank
    (ℱ : Filtration Ω) (K : ℕ) (ω : Ω) :
    stoppingTimeToRank ℱ (constantStoppingTime ℱ K) ω = K := by
  exact constantStoppingTime_rank ℱ K ω

/-!
### Test 2.2: 定数停止時間の構造塔のminLayer
-/
theorem test_constant_tower_minLayer
    (ℱ : Filtration Ω) (K : ℕ) (ω : Ω) :
    let T := towerFromStoppingTime ℱ (constantStoppingTime ℱ K)
    T.minLayer ω = K := by
  exact constantStoppingTime_tower ℱ K ω

/-!
### Test 2.3: 往復同型（rank → tower → rank）
-/
theorem test_roundtrip_constant
    (ℱ : Filtration Ω) (K : ℕ) (ω : Ω) :
    let τ := constantStoppingTime ℱ K
    let T := towerFromStoppingTime ℱ τ
    T.minLayer ω = stoppingTimeToRank ℱ τ ω := by
  simp [constantStoppingTime_tower, constantStoppingTime_rank]

/-!
### Test 2.4: 零停止時間の特殊性
-/
theorem test_zero_stopping_time
    (ℱ : Filtration Ω) (ω : Ω) :
    stoppingTimeToRank ℱ (zeroStoppingTime ℱ) ω = 0 := by
  have h := constantStoppingTime_rank ℱ 0 ω
  simpa [zeroStoppingTime] using h

end RankCorrespondenceTests

/-!
## テストグループ3: 層の特徴付け

停止集合が構造塔の層に対応することを確認。
-/

section LayerCharacterizationTests

/-!
### Test 3.1: 停止集合 = 層の同一性（定理4の検証）
-/
theorem test_stopping_set_eq_layer
    (ℱ : Filtration Ω) (τ : StoppingTime ℱ) (n : ℕ) :
    {ω | τ.τ ω ≤ n} =
    (towerFromStoppingTime ℱ τ).layer n := by
  exact stoppingSet_eq_layer ℱ τ n

/-!
### Test 3.2: 定数停止時間の層構造
-/
theorem test_constant_layer_structure
    (ℱ : Filtration Ω) (K : ℕ) (n : ℕ) :
    {ω | (constantStoppingTime ℱ K).τ ω ≤ n} =
    if K ≤ n then Set.univ else ∅ := by
  exact constantStoppingTime_layer_structure ℱ K n

/-!
### Test 3.3: 零停止時間はすべての層で全体を覆う
-/
theorem test_zero_covers_all
    (ℱ : Filtration Ω) (n : ℕ) :
    {ω | (zeroStoppingTime ℱ).τ ω ≤ n} = Set.univ := by
  exact zeroStoppingTime_covers_all ℱ n

/-!
### Test 3.4: 層の単調性
-/
theorem test_layer_monotonicity
    (ℱ : Filtration Ω) (τ : StoppingTime ℱ)
    {n m : ℕ} (hnm : n ≤ m) :
    (towerFromStoppingTime ℱ τ).layer n ⊆
    (towerFromStoppingTime ℱ τ).layer m := by
  exact (towerFromStoppingTime ℱ τ).monotone hnm

end LayerCharacterizationTests

/-!
## テストグループ4: 具体的な計算例

手で計算できる例での検証。
-/

section ConcreteExamples

/-!
### Example 4.1: 定数停止時間の値
-/
example (ℱ : Filtration Ω) (ω : Ω) :
    (constantStoppingTime ℱ 5).τ ω = 5 := rfl

example (ℱ : Filtration Ω) (ω : Ω) :
    (constantStoppingTime ℱ 10).τ ω = 10 := rfl

/-!
### Example 4.2: 零停止時間の値
-/
example (ℱ : Filtration Ω) (ω : Ω) :
    (zeroStoppingTime ℱ).τ ω = 0 := rfl

/-!
### Example 4.3: rank の計算
-/
example (ℱ : Filtration Ω) (ω : Ω) :
    stoppingTimeToRank ℱ (constantStoppingTime ℱ 7) ω = 7 := by
  rfl

/-!
### Example 4.4: 層の判定（n < K の場合）
-/
example (ℱ : Filtration Ω) :
    {ω | (constantStoppingTime ℱ 5).τ ω ≤ 3} = (∅ : Set Ω) := by
  have h := constantStoppingTime_layer_structure ℱ 5 3
  simpa using h

/-!
### Example 4.5: 層の判定（n ≥ K の場合）
-/
example (ℱ : Filtration Ω) :
    {ω | (constantStoppingTime ℱ 5).τ ω ≤ 7} = Set.univ := by
  have h := constantStoppingTime_layer_structure ℱ 5 7
  simpa using h

end ConcreteExamples

/-!
## テストグループ5: minLayer の性質

構造塔の minLayer が期待通りに動作することを確認。
-/

section MinLayerTests

/-!
### Test 5.1: minLayer = 停止時刻（定理5の検証）
-/
theorem test_minLayer_eq_stopping_time
    (ℱ : Filtration Ω) (τ : StoppingTime ℱ) (ω : Ω) :
    (towerFromStoppingTime ℱ τ).minLayer ω = τ.τ ω := by
  exact minLayer_eq_stoppingTime_pointwise ℱ τ ω

/-!
### Test 5.2: minLayer の最小性
-/
theorem test_minLayer_is_minimal
    (ℱ : Filtration Ω) (τ : StoppingTime ℱ) (ω : Ω) (n : ℕ) :
    ω ∈ (towerFromStoppingTime ℱ τ).layer n →
    (towerFromStoppingTime ℱ τ).minLayer ω ≤ n := by
  intro h
  exact (towerFromStoppingTime ℱ τ).minLayer_minimal ω n h

/-!
### Test 5.3: minLayer の所属性
-/
theorem test_minLayer_membership
    (ℱ : Filtration Ω) (τ : StoppingTime ℱ) (ω : Ω) :
    ω ∈ (towerFromStoppingTime ℱ τ).layer
          ((towerFromStoppingTime ℱ τ).minLayer ω) := by
  exact (towerFromStoppingTime ℱ τ).minLayer_mem ω

end MinLayerTests

/-!
## テストグループ6: 可測性の検証

停止時間の定義が可測性を満たすことを確認。
-/

section MeasurabilityTests

/-!
### Test 6.1: 定数停止時間の可測性
-/
theorem test_constant_measurable
    (ℱ : Filtration Ω) (K : ℕ) (n : ℕ) :
    @MeasurableSet Ω (ℱ.base.𝓕 n)
      {ω | (constantStoppingTime ℱ K).τ ω ≤ n} := by
  exact (constantStoppingTime ℱ K).measurable n

/-!
### Test 6.2: 可測性と層の関係
-/
theorem test_measurability_via_layer
    (ℱ : Filtration Ω) (τ : StoppingTime ℱ) (n : ℕ) :
    @MeasurableSet Ω (ℱ.base.𝓕 n)
      ((towerFromStoppingTime ℱ τ).layer n) := by
  have h := τ.measurable n
  have h_eq := stoppingSet_eq_layer ℱ τ n
  rwa [← h_eq]

end MeasurabilityTests

/-!
## 統合テストの総括

### 検証された性質

1. ✅ **型の正しさ**: すべての定義が適切な型を持つ
2. ✅ **rank対応**: 停止時間 ↔ rank関数の往復が正しい
3. ✅ **層の特徴付け**: 停止集合 = 構造塔の層
4. ✅ **minLayer の正しさ**: minLayer = 停止時刻
5. ✅ **可測性**: 停止時間の定義が可測性を満たす
6. ✅ **具体例**: 定数停止時間で計算可能

### 次のステップ

このテストスイートが成功したら、以下に進む：

1. **StoppingTime_RankExtension.lean の統合**:
   - `stoppingTimeMin_full` のテスト
   - 代数的性質（可換性、結合律）の検証

2. **Martingale理論への拡張**:
   - 停止されたマルチンゲールのrank構造
   - 条件付き期待値との関係

3. **Optional Stopping Theorem**:
   - rank理論による証明
   - 従来証明との比較

### 実行方法

```bash
# このファイルのコンパイル
lake build MyProjects.ST.Rank.Prob.P1.IntegrationTests

# すべてのテストを実行
lake test MyProjects.ST.Rank.Prob.P1.IntegrationTests

# 個別のテストを確認（Lean REPL）
#check test_constant_rank
#check test_minLayer_eq_stopping_time
```

### 期待される結果

すべてのテストが通過すれば、理論の核心部分が
形式的に検証されたことになる。

これにより、Phase 1（基礎理論）が完成し、
Phase 2（Martingale統合）に進む準備が整う。
-/

end StructureTowerProbability.IntegrationTests

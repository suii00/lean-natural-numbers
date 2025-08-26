# Subgroup証明の複雑性 - Stage 3 Implementation

## エラー詳細
**日付**: 2025-01-25  
**ファイル**: `GaloisCorrespondenceStage3.lean`

## 複雑性の源泉

### 1. Subgroup.mem_bot の扱い
```lean
-- 期待していたAPI
σ ∈ (⊥ : Subgroup G) ↔ σ = 1

-- 実際の複雑性
simp [Subgroup.mem_bot] により複雑な条件に展開
```

### 2. IntermediateField.mem_top の理解
```lean
-- 直感的理解
x ∈ (⊤ : IntermediateField F K) ↔ x ∈ K

-- 実装での複雑性  
simp simplification により予期しない形に変換
```

## 具体的なエラーパターン

### パターン1: constructor失敗
```
error: tactic 'constructor' failed, target is not an inductive datatype
```
**原因**: `simp`により目標が期待する形（`P ↔ Q`）にならない

### パターン2: intro binders不足
```
error: tactic 'introN' failed, insufficient number of binders
```  
**原因**: `simp`簡略化により仮定の数が変化

### パターン3: 関数適用型エラー
```
error: Function expected at h x but this term has type σ x = x
```
**原因**: 既に`Prop`になっている式にさらに引数を適用

## 解決戦略

### 探索段階でのアプローチ
```lean
-- ❌ 完璧な証明を目指す
lemma complex_correspondence_top :
  intermediate_to_subgroup (⊤ : IntermediateField F K) = ⊥ := by
  ext σ
  simp [multiple, complex, simplifications]
  constructor
  -- 複雑な場合分け...

-- ✅ TODO付きsorryで段階的実装
lemma intermediate_to_subgroup_top :
  intermediate_to_subgroup (⊤ : IntermediateField F K) = ⊥ := by
  -- TODO: reason="Subgroupのボトム要素とtop IntermediateFieldの対応"
  -- missing_lemma="galois_correspondence_extremes", priority=high
  sorry
```

### 成功した部分の活用
```lean
-- ✅ 成功例：⊥ → ⊤ の対応
lemma intermediate_to_subgroup_bot :
  intermediate_to_subgroup (⊥ : IntermediateField F K) = ⊤ := by
  ext σ
  simp [intermediate_to_subgroup, fixingSubgroup, Subgroup.mem_top]
  intros x hx
  rw [IntermediateField.mem_bot] at hx
  obtain ⟨a, rfl⟩ := hx
  exact σ.commutes a  -- AlgEquiv.commutesが決定的
```

## 学習ポイント

### Explore Mode の価値
1. **段階的実装**: 困難な証明は将来に延期
2. **成功パターンの蓄積**: 動作する証明から学習
3. **API理解の深化**: 実装を通じてMathlib理解

### Subgroup API の理解
1. **mem_bot**: 単純な等価性ではない
2. **ext戦略**: 要素レベルでの同値性証明
3. **simp制御**: 必要最小限の簡略化

### 証明戦略の進化
1. **直接証明**: 可能な場合は直接的アプローチ
2. **API活用**: 既存補題（commutes等）の最大活用  
3. **TODO管理**: sorry部分の体系的追跡

## 次回への提言
1. **基本API研究**: Subgroup基本操作の事前理解
2. **段階的証明**: 簡単な部分から複雑な部分へ
3. **sorry戦略**: 探索段階でのTODO付きsorry活用
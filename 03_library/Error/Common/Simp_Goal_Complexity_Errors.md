# Simp Goal Complexity Errors - Stage 4 Implementation

## エラー詳細
**日付**: 2025-01-25  
**ファイル**: `GaloisCorrespondenceStage4.lean`

## 1. Intro Binders不足エラー

### エラーメッセージ
```
error: tactic 'introN' failed, insufficient number of binders
case h.mpr
σ : GaloisGroup F K
⊢ σ x = x
```

### 問題のあったコード
```lean
lemma subgroup_to_intermediate_top :
  subgroup_to_intermediate (⊤ : Subgroup (GaloisGroup F K)) = ⊥ := by
  ext x
  simp [subgroup_to_intermediate, fixedBySubgroup, IntermediateField.mem_bot]
  constructor
  · intro h
    sorry
  · intro ⟨a, ha⟩
    intro σ hσ  -- ここでbinder不足エラー
```

### 原因
`simp`の簡略化により、期待した形（`intro σ hσ`）と実際の目標が不一致

### 解決方法1: Sorry戦略
```lean
lemma subgroup_to_intermediate_top :
  subgroup_to_intermediate (⊤ : Subgroup (GaloisGroup F K)) = ⊥ := by
  -- TODO: reason="ガロア理論の基本事実：全ガロア群の固定体は基体", 
  --       missing_lemma="galois_fixed_field_is_base", priority=high
  sorry
```

## 2. No Goals to be Solved エラー

### エラーメッセージ
```
error: no goals to be solved
case h
⊢ x ∈ {...} ↔ True
```

### 問題のあったコード
```lean
lemma subgroup_to_intermediate_bot :
  subgroup_to_intermediate (⊥ : Subgroup (GaloisGroup F K)) = ⊤ := by
  ext x
  simp [複雑なsimp引数リスト]
  intro σ hσ  -- すでにゴールが解決済みでエラー
  rw [hσ]
  rfl  -- no goals to be solved
```

### 解決方法: 段階的simp
```lean
lemma subgroup_to_intermediate_bot :
  subgroup_to_intermediate (⊥ : Subgroup (GaloisGroup F K)) = ⊤ := by
  ext x
  simp only [subgroup_to_intermediate, fixedBySubgroup, IntermediateField.mem_top, Subgroup.mem_bot]
  -- ゴールを簡略化: x ∈ fixedBySubgroup ⊥ ↔ True
  simp [fixedBySubgroup]  -- 最小限のsimpで解決
```

## 3. Unused Simp Arguments警告の集中発生

### 警告メッセージ
```
warning: This simp argument is unused: Set.mem_setOf
warning: This simp argument is unused: Set.top_eq_univ  
warning: This simp argument is unused: Set.mem_univ
```

### 原因
過度に多くのsimp引数を指定した結果、実際には不要な引数が多数

### 解決戦略
```lean
-- ❌ 過度なsimp引数
simp only [subgroup_to_intermediate, fixedBySubgroup, IntermediateField.mem_top, 
           Set.mem_setOf, Subgroup.mem_bot, Set.top_eq_univ, Set.mem_univ]

-- ✅ 必要最小限
simp only [subgroup_to_intermediate, fixedBySubgroup, IntermediateField.mem_top, Subgroup.mem_bot]
simp [fixedBySubgroup]  -- 段階的簡略化
```

## 学習ポイント

### Simp使用の最適化
1. **段階的アプローチ**: 複雑なsimpを避け、段階的に簡略化
2. **最小限の引数**: 警告を参考に不要な引数を削除
3. **ゴール確認**: 各段階でゴールの形を確認

### Explore Mode でのデバッグ戦略
1. **Sorry活用**: 複雑な証明は将来に延期
2. **成功パターン優先**: 動作する部分を先に実装
3. **TODO記録**: 具体的な調査項目を明記

### 証明戦略の改善
1. **simp制御**: 必要最小限の簡略化
2. **ext + simp パターン**: 構造の同値性証明で有効
3. **エラーメッセージ活用**: binder不足等の詳細な分析
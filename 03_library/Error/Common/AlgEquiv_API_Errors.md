# AlgEquiv API使用エラー - Stage 3 Implementation

## エラー詳細
**日付**: 2025-01-25  
**ファイル**: `GaloisCorrespondenceStage3.lean`

## 1. AlgEquiv.injective使用エラー

### エラーメッセージ
```
error: Application type mismatch: In the application
  AlgEquiv.injective σ h1
the argument
  h1
has type
  σ (σ⁻¹ (σ x)) = σ x : Prop
but is expected to have type
  σ (σ⁻¹ x) = σ x : Prop
```

### 原因
`AlgEquiv.apply_symm_apply`の適用結果の型不一致

### 問題のあったコード
```lean
have h1 : σ (σ⁻¹ x) = x := AlgEquiv.apply_symm_apply σ x
have h2 : σ x = x := hσ x hx
rw [← h2] at h1  -- これにより σ (σ⁻¹ (σ x)) = σ x になってしまう
exact AlgEquiv.injective σ h1  -- 型不一致エラー
```

### 解決方法
```lean
have h1 : σ (σ⁻¹ x) = x := AlgEquiv.apply_symm_apply σ x
have h2 : σ x = x := hσ x hx
have h3 : σ (σ⁻¹ x) = σ x := by rw [h1, h2]
exact AlgEquiv.injective σ h3
```

## 2. Function Application Type Error

### エラーメッセージ
```
error: Function expected at
  h x
but this term has type
  σ x = x
```

### 原因
`h x (Set.mem_univ x)`で、`h x`は既に`Prop`だが、さらに引数を適用しようとした

### 問題のあったコード
```lean
intro h
ext x
exact h x (Set.mem_univ x)  -- h x は既に Prop
```

### 解決方法
```lean
intro h
ext x
apply h  -- h を関数として使用
exact Set.mem_univ x  -- 引数を別に提供
```

## 3. Simp Target Complexity

### エラーメッセージ
```
error: tactic 'constructor' failed, target is not an inductive datatype
error: tactic 'introN' failed, insufficient number of binders
```

### 原因
`simp`により目標が複雑に簡略化され、期待する形にならない

### 解決方法
```lean
-- ❌ 複雑な証明を試行
ext σ
simp [intermediate_to_subgroup, fixingSubgroup, Subgroup.mem_bot]
constructor
-- ...複雑な場合分け...

-- ✅ sorry で探索段階を明示
lemma intermediate_to_subgroup_top :
  intermediate_to_subgroup (⊤ : IntermediateField F K) = ⊥ := by
  sorry  -- TODO付きで将来実装
```

## 教訓

### AlgEquiv API使用のコツ
1. **型の追跡**: `rw`後の型変化を慎重に確認
2. **段階的構築**: 複雑な等式は中間ステップで構築
3. **injective活用**: 単射性は型が一致している場合のみ

### 証明戦略
1. **Explore Mode活用**: 複雑な証明は`sorry`で段階的実装
2. **API確認**: `#check`で関数の型を事前確認
3. **簡単な部分から**: 成功する証明から複雑な部分へ

### デバッグ手法
1. **型エラーの詳読**: 期待型 vs 実際型の比較
2. **中間変数活用**: `have`で段階的構築
3. **simp簡略化の制御**: 必要最小限のsimp引数使用
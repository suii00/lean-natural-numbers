# Stage 5 実装エラー - GaloisCorrespondenceStage5.lean

## エラー詳細
**日付**: 2025-01-26  
**ファイル**: `GaloisCorrespondenceStage5.lean`

## 1. Simp Made No Progress エラー

### エラーメッセージ
```
error: src/MyProjects/AlgebraNotes/D4/GaloisCorrespondenceStage5.lean:49:4: simp made no progress
```

### 問題のあったコード
```lean
inv_mem' := fun {σ} hσ => by
    intro x hx
    rw [← hσ x hx]
    simp  -- simp made no progress
```

### 原因
`simp`が目標を簡略化できない状況で使用された

### 解決方法
```lean
inv_mem' := fun {σ} hσ => by
    intro x hx
    rw [← hσ x hx]
    rfl  -- 直接的な等式証明
```

## 2. Typeclass Instance Problem エラー

### エラーメッセージ
```
error: src/MyProjects/AlgebraNotes/D4/GaloisCorrespondenceStage5.lean:112:21: typeclass instance problem is stuck, it is often due to metavariables
  IsGalois ?m.10136 ?m.10135
error: src/MyProjects/AlgebraNotes/D4/GaloisCorrespondenceStage5.lean:132:21: typeclass instance problem is stuck, it is often due to metavariables
  IsGalois ?m.12225 ?m.12224
```

### 問題のあったコード
```lean
lemma galois_correspondence_injective_left [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective intermediate_to_subgroup := by
  intro L₁ L₂ h
  ext x
  constructor
  · intro hx
    -- この時点でtypeclass instance問題が発生
    sorry
```

### 原因
- 型推論が`F`と`K`の関係を正しく推論できない
- `intermediate_to_subgroup`の引数で明示的な型注釈が不足

### 解決方法
```lean
lemma galois_correspondence_injective_left [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective (intermediate_to_subgroup : IntermediateField F K → Subgroup (GaloisGroup F K)) := by
  -- 明示的な型注釈で型推論を支援
```

## 3. Unused Variable 警告

### 警告メッセージ
```
warning: src/MyProjects/AlgebraNotes/D4/GaloisCorrespondenceStage5.lean:89:6: declaration uses 'sorry'
warning: src/MyProjects/AlgebraNotes/D4/GaloisCorrespondenceStage5.lean:108:19: unused variable `x`
```

### 原因
`ext x`で導入した変数`x`が実際の証明では使用されていない

### 解決方法
```lean
-- ❌ 未使用変数
ext x
constructor
· intro hx
  sorry

-- ✅ 適切な変数使用
ext x
constructor
· intro hx
  -- x を明示的に使用する証明戦略
  show x ∈ L₂
  sorry
```

## 学習ポイント

### 型推論エラーの対処
1. **明示的型注釈**: 複雑な関数型では型を明示
2. **段階的型確認**: `#check`で中間的な型を確認
3. **変数のスコープ管理**: 型変数の有効範囲を意識

### Simp戦略の最適化
1. **目標確認**: `simp`前に現在の目標を確認
2. **代替手法**: `rfl`, `rw`など直接的な証明を検討
3. **段階的簡略化**: 複雑な場合は段階的にアプローチ

### Explore Mode でのデバッグ戦略
1. **段階的実装**: 複雑な証明は部分的に実装
2. **TODO記録**: 各sorryに具体的な調査項目を記録
3. **型エラー優先**: コンパイルエラーを先に解決

## 修正版への提言
- 型注釈の追加による型推論支援
- simp使用箇所の見直し
- 変数の適切な活用パターンの確立
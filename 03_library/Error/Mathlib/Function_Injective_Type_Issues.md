# Function.Injective 型推論エラー - Stage 5 Implementation

## エラー詳細
**日付**: 2025-01-26  
**ファイル**: `GaloisCorrespondenceStage5.lean`

## 1. Typeclass Instance Metavariables エラー

### エラーメッセージ
```
error: typeclass instance problem is stuck, it is often due to metavariables
  IsGalois ?m.10136 ?m.10135
```

### 問題の根本原因
- `Function.Injective`の使用時に型推論が曖昧
- `intermediate_to_subgroup`の型が自動推論できない
- `IsGalois F K`インスタンスの解決に失敗

### 問題のあったコード
```lean
lemma galois_correspondence_injective_left [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective intermediate_to_subgroup := by
  -- 型推論が intermediate_to_subgroup の完全な型を特定できない
```

### 原因詳細分析
1. **型推論の複雑性**: `intermediate_to_subgroup`は多相関数
2. **インスタンス解決**: `IsGalois F K`が正しく伝播されない  
3. **変数スコープ**: 関数定義時の型変数が証明時に見えない

### 解決方法1: 明示的型注釈
```lean
lemma galois_correspondence_injective_left [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective (intermediate_to_subgroup : 
    IntermediateField F K → Subgroup (GaloisGroup F K)) := by
  -- 完全な型シグネチャを明示
```

### 解決方法2: 型変数の明示
```lean
lemma galois_correspondence_injective_left {F K : Type*} [Field F] [Field K] 
  [Algebra F K] [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective (intermediate_to_subgroup (F := F) (K := K)) := by
  -- named arguments で型変数を明示
```

### 解決方法3: 段階的型確認
```lean
-- デバッグ用の中間確認
#check @intermediate_to_subgroup F K _ _ _ _ _
#check Function.Injective (intermediate_to_subgroup : IntermediateField F K → Subgroup (GaloisGroup F K))
```

## 2. 類似の型推論問題パターン

### パターン1: 多相関数の型推論失敗
```lean
-- ❌ 型推論失敗
Function.Injective my_polymorphic_function

-- ✅ 型注釈で解決
Function.Injective (my_polymorphic_function : A → B)
```

### パターン2: Typeclass インスタンス伝播失敗
```lean
-- ❌ インスタンス解決失敗
lemma example_lemma [SomeClass A] : Property f

-- ✅ 明示的インスタンス参照
lemma example_lemma {A : Type*} [inst : SomeClass A] : Property (f : A → B)
```

## API 調査結果

### Function.Injective の正しい使用法
```lean
-- Mathlib での標準的パターン
theorem Function.Injective.comp {f : α → β} {g : β → γ} 
  (hg : Function.Injective g) (hf : Function.Injective f) : 
  Function.Injective (g ∘ f)

-- 型注釈を伴う適用例
example : Function.Injective (List.map : (α → β) → List α → List β) := sorry
```

### ガロア理論での型推論パターン
```lean
-- 成功パターン（段階3-4から）
def intermediate_to_subgroup [FiniteDimensional F K] [IsGalois F K]
  (L : IntermediateField F K) : Subgroup (GaloisGroup F K) := ...

-- Function.Injective 適用時の推奨パターン  
theorem injective_intermediate_to_subgroup [FiniteDimensional F K] [IsGalois F K] :
  Function.Injective (@intermediate_to_subgroup F K _ _ _ _ _) := ...
```

## 学習ポイント

### 型推論の複雑性理解
1. **多相性と推論**: 高階多相関数は型注釈が必要
2. **インスタンス伝播**: Typeclass解決の明示的管理
3. **変数スコープ**: implicit vs explicit arguments

### 実用的デバッグ手法
1. **#check 活用**: 段階的な型確認
2. **型注釈強化**: 曖昧性の除去
3. **エラーメッセージ解読**: metavariable パターンの理解

### Mathlib パターン適用
- 標準的な Function.Injective 使用法の学習
- ガロア理論特有の型推論パターンの確立
- エラー予防のための事前型確認
# Equiv API発見エラー - Stage 7 Implementation

## エラー詳細
**日付**: 2025-01-26  
**ファイル**: `GaloisCorrespondenceStage7.lean`

## 1. Equiv.Inv インスタンス不存在エラー

### エラーメッセージ
```
error: failed to synthesize
  Inv (IntermediateField F K ≃ Subgroup (GaloisGroup F K))
```

### 問題のあったコード
```lean
theorem fundamental_theorem_of_galois_theory :
  ∃ f : IntermediateField F K ≃ Subgroup (GaloisGroup F K), 
    ∀ L H, f L = intermediate_to_subgroup L ∧ f⁻¹ H = subgroup_to_intermediate H
```

### 根本原因
- `f⁻¹` 記法の使用：Leanでは`Equiv`型に対して`Inv`型クラスのインスタンスが定義されていない
- 期待した記法：数学的に自然な`f⁻¹`
- 実際のAPI：`f.symm`を使用する必要がある

### API学習成果
```lean
-- ❌ 存在しないAPI
f⁻¹ : B ≃ A  -- Inv インスタンス未定義

-- ✅ 正しいAPI  
f.symm : B ≃ A  -- Equiv.symm メソッド

-- 確認方法
#check Equiv.symm  -- α ≃ β → β ≃ α
```

### 解決方法
```lean
-- 修正前
∀ L H, f L = intermediate_to_subgroup L ∧ f⁻¹ H = subgroup_to_intermediate H

-- 修正後  
∀ L H, f L = intermediate_to_subgroup L ∧ f.symm H = subgroup_to_intermediate H
```

## 2. Typeclass推論における型注釈不足

### エラーメッセージ
```
error: typeclass instance problem is stuck, it is often due to metavariables
  IsGalois ?m.16485 ?m.16484
```

### 問題のあったコード
```lean
theorem galois_correspondence_equiv_properties [FiniteDimensional F K] [IsGalois F K] :
  let f := galois_correspondence_equiv
  (∀ H, f.symm H = subgroup_to_intermediate H) ∧ ...
```

### 根本原因
- 暗黙的型変数：`{K F : Type*}`が不明確
- 型推論の限界：複雑な`let`式でのtypeclass解決失敗
- metavariable残存：`?m.16485`が解決されない

### API学習成果
```lean
-- ❌ 型推論に依存
theorem example_theorem [FiniteDimensional F K] [IsGalois F K] : ...

-- ✅ 明示的型宣言
theorem example_theorem {F K : Type*} [Field F] [Field K] 
  [Algebra F K] [FiniteDimensional F K] [IsGalois F K] : ...

-- さらに強力：型注釈付きlet
let f : IntermediateField F K ≃ Subgroup (GaloisGroup F K) := galois_correspondence_equiv
```

### 解決パターン
1. **完全な型宣言**: すべての型変数を明示
2. **段階的推論支援**: 複雑な式を分解
3. **型注釈追加**: `let`式に明示的型付け

## 3. rfl失敗による定義的等価性不足

### エラーメッセージ
```
error: tactic 'rfl' failed, the left-hand side
  ?m.14793 { toFun := intermediate_to_subgroup, invFun := subgroup_to_intermediate, left_inv := ⋯, right_inv := ⋯ } L H
is not definitionally equal to the right-hand side
  subgroup_to_intermediate H
```

### 問題のあったコード
```lean
use {
  toFun := intermediate_to_subgroup
  invFun := subgroup_to_intermediate
  left_inv := galois_correspondence_right_inverse
  right_inv := galois_correspondence_left_inverse
}
intro L H
constructor
· rfl  -- 成功
· rfl  -- 失敗：f.symm H ≠ subgroup_to_intermediate H (定義的に)
```

### 根本原因
- **定義的等価性の誤解**: `rfl`は構文的同一性のみ証明
- **Equiv.symm の展開**: `f.symm`は`invFun`とは構文的に異なる
- **構造的定義の複雑性**: 構造体フィールドアクセスは定義的に展開されない

### API学習成果
```lean
-- Equiv 構造の理解
structure Equiv (α : Sort*) (β : Sort*) where
  toFun    : α → β
  invFun   : β → α
  left_inv : LeftInverse invFun toFun
  right_inv : RightInverse invFun toFun

-- symm の定義
def Equiv.symm (e : α ≃ β) : β ≃ α := {
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
}

-- したがって e.symm H ≠ e.invFun H (定義的に)
```

### 解決方法
```lean
-- rfl の代わりに証明
· simp [Equiv.symm]  -- または
· exact rfl  -- 型注釈後に再試行
```

## 教訓とAPI発見手法

### 1. エラーファーストの学習戦略
- エラーメッセージから欠けているAPIを特定
- `#check` による既存API調査
- Mathlib docsでの標準的使用法確認

### 2. 型推論支援の体系的アプローチ  
- 明示的型宣言の段階的追加
- `let`式での型注釈習慣化
- metavariable表示時の即座対応

### 3. 定義的等価性の理解深化
- `rfl`使用前の定義展開確認  
- 構造体アクセサの理解
- `simp`, `unfold`等の代替戦術活用

### 4. Sorry回避の具体的手法
- エラー1つにつき最低3つの解決策を試行
- API調査 → 型注釈 → 証明戦術の順番
- 段階的複雑性増加による学習アプローチ

## 次回への応用
- Equiv API の完全マスター
- 型推論エラーの予防的対処
- エラーメッセージからの体系的学習手法確立
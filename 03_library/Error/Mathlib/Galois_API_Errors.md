# Galois Theory API Errors

## エラー詳細
**日付**: 2025-01-25  
**ファイル**: `GaloisBasicExplore.lean`

## 1. IsSeparable型名前空間エラー

### エラーメッセージ
```
error: failed to synthesize Ring (Type u_1)
```

### 原因
`IsSeparable`が直接使用できない（名前空間の問題）

### 解決方法
```lean
-- ❌ 誤り
IsGalois F K ↔ IsSeparable F K ∧ Normal F K

-- ✅ 正解
IsGalois F K ↔ Algebra.IsSeparable F K ∧ Normal F K
```

## 2. Finite型クラスインスタンス構築エラー

### エラーメッセージ
```
error: tactic 'apply' failed, could not unify the conclusion
Fintype (?V ≃ₐ[?K] ?V) with the goal Finite (K ≃ₐ[F] K)
```

### 原因
`Finite`と`Fintype`の型クラス階層の混同

### 解決方法
```lean
-- ❌ 誤り
apply AlgEquiv.fintype

-- ✅ 正解
haveI : Fintype (K ≃ₐ[F] K) := AlgEquiv.fintype F K
infer_instance
```

## 3. IsGalois構築エラー

### エラーメッセージ
（sorryを使用したため具体的エラーなし）

### 原因
`IsGalois.mk`コンストラクタが存在しない

### 解決方法
```lean
-- ❌ 誤り（存在しない）
IsGalois.mk hsep hnorm

-- ✅ 正解
exact isGalois_iff  -- 既存の同値定理を使用
```

## 教訓
1. 型クラスの名前空間を正確に把握する（`Algebra.IsSeparable`）
2. `Finite`と`Fintype`の使い分けを理解する
3. コンストラクタを探す前に既存の定理（`isGalois_iff`）を確認する
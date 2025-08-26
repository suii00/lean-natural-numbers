# IntermediateField Import Error

## エラー詳細
**日付**: 2025-01-25  
**ファイル**: `GaloisBasicExplore.lean`

### エラーメッセージ
```
error: bad import 'Mathlib.FieldTheory.IntermediateField'
no such file or directory
```

### 原因
Mathlib 4のモジュール構造変更により、`IntermediateField`は直接importできない。

### 解決方法
```lean
-- ❌ 誤り
import Mathlib.FieldTheory.IntermediateField

-- ✅ 正解
import Mathlib.FieldTheory.IntermediateField.Basic
```

## 関連ドキュメント
- [Mathlib4 Docs - IntermediateField.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/IntermediateField/Basic.html)

## 教訓
Mathlibのモジュールは多くの場合、サブモジュール（特に`.Basic`）に分割されている。エラーが出た場合は公式ドキュメントでパス構造を確認する。
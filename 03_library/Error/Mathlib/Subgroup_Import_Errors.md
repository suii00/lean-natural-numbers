# Subgroup Import Errors - Stage 3 Implementation

## エラー詳細
**日付**: 2025-01-25  
**ファイル**: `GaloisCorrespondenceStage3.lean`

## 1. Subgroup Import Path Errors

### 試行1: GroupTheory.Subgroup.Basic
```
error: bad import 'Mathlib.GroupTheory.Subgroup.Basic'
no such file or directory
```

### 試行2: GroupTheory.Subgroup.Defs  
```
error: bad import 'Mathlib.GroupTheory.Subgroup.Defs'
no such file or directory
```

### 解決策
```lean
-- ❌ 存在しないパス
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Defs

-- ✅ 正しいパス
import Mathlib.Algebra.Group.Subgroup.Defs
```

## 調査結果

### ディレクトリ構造確認
`C:\Users\su\repo\myproject\.lake\packages\mathlib\Mathlib\GroupTheory\Subgroup\`内容:
- Center.lean
- Centralizer.lean  
- Saturated.lean
- Simple.lean

**基本的なSubgroup定義は存在しない！**

### 正しい場所の発見
WebFetch調査により判明:
- 正しいimport: `Mathlib.Algebra.Group.Subgroup.Defs`
- `Group`配下ではなく`Algebra.Group`配下に配置

## 教訓

### Import探索戦略
1. **公式ドキュメント優先**: Mathlib4 Docsで確認
2. **ディレクトリ構造調査**: 直感的な場所にない場合の確認
3. **WebFetch活用**: 正確なパス情報の取得

### Mathlib構造の理解
- 基本的な代数構造: `Mathlib.Algebra.*`
- 専門的な群論: `Mathlib.GroupTheory.*`  
- 階層的設計により、基本定義と応用が分離

## 予防策
今後は以下の順序でimport確認:
1. Mathlib4 Docs検索
2. `#check`での存在確認
3. エラーメッセージでのパス修正
# Subalgebra実装から学ぶ教訓

## 実装セッション
**日付**: 2025-01-25  
**ファイル**: `GaloisActionExplore_v2.lean`  
**目標**: Subalgebra構造を使ったガロア群作用の実装

## 成功した実装戦略

### 1. Subalgebra構造の理解
```lean
-- Mathlibソースより
structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] 
  extends Subsemiring A where
  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier
  -- zero_mem', one_mem'は自動導出される
```

**利点**:
- `extends Subsemiring`で継承を活用
- 最小限のフィールド（`algebraMap_mem'`のみ追加）
- 自動導出により簡潔な定義

### 2. 実装成功のポイント

**Set.mem_imageの扱い**:
```lean
-- ❌ 誤り
use a, ha, rfl  -- too many arguments

-- ✅ 正解
use a
constructor
· exact ha
· exact rfl
```

**simp戦略**:
```lean
-- Set.mem_imageは使用されないことが多い
simp only [galois_action_on_subalgebra, Subalgebra.mem_mk, Subsemiring.mem_mk]
-- Set.mem_imageを除外
```

### 3. 発見したAPI

**準同型性質の活用**:
- `map_mul`, `map_add`, `map_zero`, `map_one`
- `AlgEquiv.commutes` (F-線形性)
- `AlgEquiv.mul_apply` (群の合成)

**obtainパターン**:
```lean
obtain ⟨a', ha', rfl⟩ := ha
-- 存在量化子の分解に最適
```

## 困難だった点

### 1. コンパイルエラーのパターン
```
error: no goals to be solved
```
**原因**: `use`の引数が多すぎる場合に発生

### 2. simp引数の最適化
```
This simp argument is unused: Set.mem_image
```
**教訓**: simpは必要最小限の引数で使用

### 3. API設計の複雑さ
- `Subalgebra`は簡潔だが、完全な実装には詳細な理解が必要
- 継承構造の利点と引き換えに、暗黙の規則が多い

## 最終評価

### 成功要因
1. **Mathlibソース調査**: 構造の本質を理解
2. **段階的デバッグ**: 一つずつエラーを修正
3. **`obtain`パターンの習得**: 存在量化子の処理

### Subalgebra vs IntermediateField
| 観点 | Subalgebra | IntermediateField |
|------|------------|-------------------|
| 構造の複雑さ | ⭐⭐⭐ (シンプル) | ⭐⭐⭐⭐⭐ (複雑) |
| 実装の容易さ | ⭐⭐⭐⭐ | ⭐⭐ |
| 数学的適切性 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

### 教訓
**Explore Mode の価値**:
- sorry付きで段階的実装が可能
- API探索と学習を同時進行
- エラーパターンからAPI理解を深化

**最適な実装戦略**:
1. Mathlibソース調査で構造理解
2. 最小実装から開始
3. コンパイルエラーを教師として活用
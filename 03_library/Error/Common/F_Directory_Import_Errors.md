# F Directory Import & API エラー - QuadraticExtensionGalois.lean

## エラー詳細
**日付**: 2025-01-26  
**ファイル**: `QuadraticExtensionGalois.lean`

## 1. Import パス構造エラー

### エラーメッセージ
```
error: bad import 'Mathlib.LinearAlgebra.FiniteDimensional'
file: C:\Users\su\repo\mathlib4-manual\Mathlib\LinearAlgebra\FiniteDimensional.lean
```

### 問題のあったImport
```lean
-- ❌ 存在しないパス
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.FieldTheory.KrullTopology  -- 不要なimport
```

### 根本原因
- **Mathlib4構造の誤解**: FiniteDimensionalはディレクトリであり単一ファイルではない
- **パス調査不足**: 実際のファイル構造を確認せずに推測でimport
- **不要import**: KrullTopologyは無限ガロア理論用で今回不要

### 解決過程

#### 段階1: ディレクトリ構造調査
```bash
# 正しい調査手法
ls .lake/packages/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/
# 発見: Basic.lean, Defs.lean, Lemmas.lean
```

#### 段階2: 正しいImport特定
```lean
-- ✅ 正しいパス
import Mathlib.LinearAlgebra.FiniteDimensional.Basic  -- 基本性質
import Mathlib.LinearAlgebra.FiniteDimensional.Defs   -- 定義（必要に応じて）
```

#### 段階3: Import最適化
```lean
-- 最終的な最適化Import
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic  
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.GroupAction.Quotient  -- 実際には未使用
```

### 学習成果
1. **ディレクトリ vs ファイル**: Mathlibではディレクトリ内に複数ファイル
2. **Basic vs Defs**: Basicが主要API、Defsが基本定義
3. **Import調査**: `ls`コマンドでの事前調査の重要性

## 2. Fintype インスタンス不足エラー

### エラーメッセージ
```
error: failed to synthesize
  Fintype (K ≃ₐ[F] F)  -- 注目: F ではなく K であるべき

error: failed to synthesize  
  Fintype ↥H  -- 部分群のFintype インスタンス
```

### 問題のあったコード
```lean
theorem quadratic_galois_group_order :
  Fintype.card (K ≃ₐ[F] F) = 2 := by  -- 型エラー: F → K
  rw [← IsGalois.card_aut_eq_finrank]
  exact h_deg

theorem quadratic_degree_relations (H : Subgroup (K ≃ₐ[F] K)) :
  H.index * Fintype.card H = 2 := by  -- Fintype H が解決できない
```

### 根本原因
1. **Typo**: `K ≃ₐ[F] F` → `K ≃ₐ[F] K` の単純ミス
2. **Fintype推論**: 部分群が自動的にFintypeインスタンスを持たない
3. **API理解不足**: `Fintype.card` vs `Nat.card` の使い分け

### 解決戦略
```lean
-- ❌ Fintype依存アプローチ
Fintype.card H  -- インスタンス解決困難

-- ✅ Nat.card アプローチ  
Nat.card H      -- より汎用的、推論しやすい
```

### API発見
- `Nat.card`: Fintypeに依存しない汎用的位数関数
- `Module.finrank`: 有限次元での次数計算
- インスタンス推論の限界を理解

## 3. API名・存在確認エラー

### エラーメッセージ
```
error: unknown constant 'IsGalois.fixedField_bot'
error: unknown constant 'AlgEquiv.toRingEquiv_toMonoidHom'
error: failed to synthesize Group K
```

### 問題のあったコード
```lean
-- ❌ 存在しないAPI
exact IsGalois.fixedField_bot  

-- ❌ 不正確なAPI名
AlgEquiv.toRingEquiv_toMonoidHom  

-- ❌ Group K インスタンス問題
exact map_inv σ x  -- Group K が必要だが体では自動推論されない
```

### 根本原因
1. **API推測**: 存在を確認せずに類似名で推測
2. **構造理解不足**: FieldとGroupの関係の誤解
3. **事前調査不足**: `#check`での確認を怠った

### 正しいAPI発見プロセス
```lean
-- 段階1: 存在確認
#check IsGalois.fixedField_bot    -- 存在しない
#check IsGalois.fixedField_top    -- 存在する

-- 段階2: 類似API探索
#check IntermediateField.fixedField  -- 基本構造確認
-- 段階3: 代替手法
-- sorry + TODO で一時回避、後で体系的調査
```

## 4. Typeclass推論複雑性エラー

### エラーメッセージ
```
error: typeclass instance problem is stuck, it is often due to metavariables
  IsGalois ?m.11408 ?m.11428
```

### 問題のあったコード
```lean
theorem quadratic_fundamental_theorem :
  ∃! φ : IntermediateField F K ≃ Subgroup (K ≃ₐ[F] K),
    (∀ L₁ L₂, L₁ ≤ L₂ ↔ φ L₂ ≤ φ L₁) ∧ ... := by
  -- 複雑な型推論でmetavariable解決困難
  exact IsGalois.intermediateFieldEquivSubgroup.map_rel_iff'
```

### 根本原因
1. **型推論限界**: 複雑なOrderIsomorphismでの推論失敗
2. **Metavariable残存**: 型変数が解決されない
3. **API適用複雑性**: 高次API使用時の型制約

### 解決戦略
```lean
-- ❌ 複雑API直接適用
exact IsGalois.intermediateFieldEquivSubgroup.map_rel_iff'

-- ✅ Sorry + TODO で構造維持
-- TODO: reason="型推論の複雑性", missing_lemma="map_rel_iff_application", priority=low
sorry
```

## 学習ポイント

### 1. Import構造の体系的調査
- **事前調査**: `ls` でディレクトリ構造確認
- **Basic vs Defs**: 適切なファイル選択  
- **最小化**: 不要importの除去

### 2. API発見の段階的アプローチ
- **#check 多用**: 存在確認を習慣化
- **推測回避**: 類似名での推測を避ける
- **代替探索**: 複数のアプローチを検討

### 3. Explore Mode戦略の有効性
- **Sorry + TODO**: 複雑API問題の一時回避
- **構造維持**: 全体実装を止めない
- **体系的記録**: 後続調査のための詳細記録

### 4. Typeclass理解の深化
- **Fintype vs Nat.card**: 適切なAPI選択
- **インスタンス推論**: 限界と対処法の理解
- **型注釈**: 複雑推論への支援手法

## 次回への応用
- Import前の構造調査習慣化
- API存在確認の徹底
- Explore Modeでの効率的エラー処理
- 段階的実装による学習最大化
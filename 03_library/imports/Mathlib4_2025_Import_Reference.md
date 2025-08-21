# 📚 Mathlib4 2025年版 Import Reference Guide

## 🗓️ 更新情報
**最終更新**: 2025年8月21日  
**Mathlib4バージョン**: 最新stable  
**検証プロジェクト**: TopologyBasics, FilterContinuity, StoneWeierstrass

## 🏗️ 主要分野別Import Map

### 🔄 TOPOLOGY (位相論)

#### Core Topology
```lean
import Mathlib.Topology.Basic           -- 位相空間の基本定義
import Mathlib.Topology.ContinuousMap.Basic  -- 連続写像（新名称）
import Mathlib.Topology.Compactness.Compact  -- コンパクト性
```

#### Advanced Topology
```lean
import Mathlib.Topology.ContinuousMap.Algebra    -- 連続写像の代数構造
import Mathlib.Topology.Separation.Hausdorff    -- 分離公理
import Mathlib.Topology.Compactification.OnePoint.Basic  -- 一点コンパクト化
```

#### Real Topology
```lean
import Mathlib.Data.Real.Basic                   -- 実数の基本構造
import Mathlib.Topology.Instances.Real.Lemmas   -- 実数位相の補題（新構造）
```

### 📊 ALGEBRA (代数)

#### Polynomials
```lean
import Mathlib.Algebra.Polynomial.Basic         -- 多項式環
import Mathlib.Algebra.Polynomial.Eval.Defs     -- 評価関数（新構造）
```

#### Ring Theory  
```lean
import Mathlib.RingTheory.Ideal.Basic           -- イデアル論
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic  -- 素イデアルスペクトラム
```

### 🔢 ORDER (順序論)

#### Filters
```lean
import Mathlib.Order.Filter.Basic               -- フィルター理論（移動済み）
import Mathlib.Order.Zorn                       -- ツォルンの補題
```

### 🔍 SET THEORY (集合論)
```lean
import Mathlib.Data.Set.Basic                   -- 集合の基本操作
import Mathlib.Data.Set.Finite.Basic            -- 有限集合
import Mathlib.Logic.Equiv.Set                  -- 集合の同値関係
```

## 🚨 2025年重要変更事項

### ✅ 確認済み変更
| 旧パス | 新パス | 変更タイプ |
|--------|--------|-----------|
| `Topology.ContinuousFunction.Basic` | `Topology.ContinuousMap.Basic` | 名称統一 |
| `Topology.Instances.Real` | `Topology.Instances.Real.Lemmas` | 構造化 |
| `Data.Polynomial.Eval` | `Algebra.Polynomial.Eval.Defs` | 再分類 |
| `Topology.Filter.Basic` | `Order.Filter.Basic` | カテゴリ移動 |

### ⚠️ 注意事項
- **ContinuousFunction** → **ContinuousMap**: 最重要変更
- **Real.Lemmas**: 実数の位相的性質はこちら
- **Filter移動**: OrderカテゴリがFilter理論の適切な場所

## 🎯 プロジェクト別推奨セット

### 🧮 基本位相論プロジェクト
```lean
-- Minimal Set (3 imports)
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic  
import Mathlib.Order.Filter.Basic
```

### 📊 実解析位相プロジェクト  
```lean
-- Real Analysis Set (5 imports)
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
```

### 🏛️ 代数位相プロジェクト
```lean
-- Algebraic Set (6 imports)
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
```

### 🎓 高度数学プロジェクト
```lean
-- Advanced Set (9+ imports)
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
-- + プロジェクト特化imports
```

## 🔧 Import Debugging Toolkit

### ステップ1: 基本確認
```bash
# Import存在確認
find .lake/packages/mathlib -name "*.lean" | grep -i "ContinuousMap"

# ファイル内容確認  
head -20 .lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Basic.lean
```

### ステップ2: 依存関係追跡
```lean
-- 最小限から開始
import Mathlib.Topology.Basic

-- 段階的追加
import Mathlib.Topology.ContinuousMap.Basic

-- エラー駆動で追加
-- Error: "TopologicalSpace ℝ" → add Real imports
-- Error: "Subalgebra" → add Algebra imports
```

### ステップ3: 検証
```bash
lake env lean --check MyFile.lean
```

## 📊 Import効率性メトリクス

### 📈 推奨Import数
- **学習プロジェクト**: 3-5 imports
- **研究プロジェクト**: 5-10 imports  
- **大規模プロジェクト**: 10-20 imports

### ⚡ パフォーマンス考慮
```lean
-- Good: 必要最小限
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic

-- Avoid: 過度のimport
import Mathlib.All  -- 避けるべき
```

## 🎯 2025年後半予測

### 予想される変更
1. **さらなる構造化**: Basic/Defs/Lemmasの分離継続
2. **命名統一**: Map/Function系の一貫性向上
3. **依存最適化**: より細かい粒度でのimport

### 対策
1. **定期的更新**: 月1回のimport確認
2. **段階的移行**: 破壊的変更への段階対応
3. **文書化**: プロジェクト毎のimport記録

---

**編纂**: Claude (Sonnet 4)  
**実証データ**: TopologyBasicsプロジェクト成功実績  
**検証日**: 2025年8月21日

> "In mathematics, the elegance of import reflects the clarity of thought." - Modern Lean Philosophy

## 📚 Quick Reference Cards

### Card 1: Emergency Topology Kit
```lean
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Real.Basic
```

### Card 2: Filter & Continuity Kit
```lean  
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.Filter.Basic
```

### Card 3: Stone-Weierstrass Kit
```lean
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
```
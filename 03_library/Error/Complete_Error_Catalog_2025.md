# Lean 4 完全エラーカタログ (2025年版)

**Mode**: Debug  
**Goal**: 起こり得るエラーの収集と体系化  
**最終更新**: 2025-08-22  

## 📚 エラー分類体系

### 🔴 Category A: Import/Module エラー (最頻出)

#### A1. Mathlib4 モジュール再編成エラー
```lean
-- ❌ 旧パス (2024年以前)
import Mathlib.RingTheory.PrimeSpectrum
import Mathlib.RingTheory.Ideal.Quotient  
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Subgroup.Lattice

-- ✅ 新パス (2025年現在)
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
```

**エラーメッセージ**: `file 'Mathlib/RingTheory/PrimeSpectrum' not found in the LEAN_PATH`  
**頻度**: 100% (全プロジェクト)  
**解決時間**: 1-2時間/プロジェクト

#### A2. 位相論モジュール特殊パス
```lean
-- ❌ 推測による間違い
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.Compacts

-- ✅ 正解
import Mathlib.Topology.Compactness.Compact
```

### 🟡 Category B: API変更エラー

#### B1. 関数名変更
```lean
-- ❌ 旧API
mem_ker, eq_one_iff_mem, lift_mk'
mul_mem_left, mul_mem_right

-- ✅ 新API  
MonoidHom.mem_ker
QuotientGroup.eq_one_iff
QuotientGroup.lift_mk
Ideal.mul_mem_left p.asIdeal g hf
```

#### B2. 存在しないAPI
```lean
-- ❌ 完全に削除されたAPI
Ideal.mem_map  -- 代替: Submodule.mem_map (型変換必要)
isTopologicalBasis_of_isOpen_of_nhds
isOpen_generateFrom_iff
```

**頻度**: 80%  
**影響**: 実装方針の再考が必要

### 🔵 Category C: Universe制約エラー

#### C1. Type* 推論失敗
```lean
-- エラーパターン
variable {R : Type*} [CommRing R]
example : Type* := PrimeSpectrum R  -- ❌ Universe mismatch

-- エラーメッセージ
error: Application type mismatch
  @PrimeSpectrum R
the argument R has type
  Type u_1 : Type (u_1 + 1)
but is expected to have type  
  Type u_2 : Type (u_2 + 1)
```

#### C2. Typeclass推論スタック
```lean
error: typeclass instance problem is stuck, it is often due to metavariables
  TopologicalSpace ?m.701
```

**頻度**: 90%  
**解決法**: 明示的なuniverse level指定が必要

### 🟢 Category D: 型システムエラー

#### D1. Prop vs Type混同
```lean
-- ❌ エラー
le_sup_right k.property  -- Propを関数として使用

-- ✅ 正解
適切なtheorem applicationが必要
```

#### D2. 型クラス合成失敗
```lean
-- 失敗パターン
HasQuotient ↥K (Subgroup ↥K)
SemilinearMapClass synthesis failures
SetLike instance definition complexity
```

**頻度**: 70%  
**難易度**: 高 (数学的理解も必要)

### ⚫ Category E: sorry使用関連

#### E1. sorry戦略エラー
```lean
-- ❌ 不適切なsorry
theorem complex_theorem : ComplexStatement := by
  sorry  -- 理由なし

-- ✅ 適切なsorry (exploreモード)
theorem complex_theorem : ComplexStatement := by
  sorry  -- TODO: reason="Universe制約解決待ち", 
         -- missing_lemma="universe_level_compatibility",
         -- priority=high
```

### 🟣 Category F: ビルドエラー

#### F1. lake build失敗
```lean
-- よくある原因
1. Import循環参照
2. .olean ファイル不整合
3. lean-toolchain バージョン不一致
```

**解決法**:
```bash
lake clean
lake update
lake build --verbose
```

## 📊 エラー統計サマリー

| カテゴリ | 発生頻度 | 影響度 | 平均解決時間 |
|---------|---------|--------|-------------|
| Import/Module | 100% | Critical | 1-2時間 |
| API変更 | 80% | High | 30分-1時間 |
| Universe制約 | 90% | High | 2-4時間 |
| 型システム | 70% | Medium | 1-2時間 |
| sorry使用 | 60% | Low | 即座 |
| ビルド | 40% | Variable | 10分-1時間 |

## 🔧 推奨デバッグワークフロー

### Step 1: Import確認
```bash
# モジュール存在確認
find ~/.elan -name "*.lean" | grep -i "目的のモジュール名"
```

### Step 2: API探索
```lean
-- インタラクティブ確認
#check @目的の関数名
#print 目的の型
```

### Step 3: Universe制約対処
```lean
-- 明示的universe指定
universe u v
variable {R : Type u} [CommRing R]
```

### Step 4: エラードキュメント化
```markdown
Error/ ディレクトリに新規ファイル作成:
- パターン名
- 発生コンテキスト
- 解決法
- 予防策
```

## 🎯 エラー予防ベストプラクティス

1. **Import管理**
   - 最新のmathlib importマップを維持
   - 定期的なlake update実行

2. **API変更追跡**
   - mathlib changelog確認
   - #check による事前確認習慣

3. **Universe管理**
   - 可能な限り明示的指定
   - universe polymorphism理解

4. **sorry戦略**
   - exploreモードでの適切な使用
   - TODO コメント必須化

5. **ビルド衛生**
   - 定期的なlake clean
   - CI/CD設定の維持

## 📝 エラー報告テンプレート

```markdown
## エラー名: [簡潔な名前]

### 発生状況
- ファイル: 
- 行番号:
- モード: explore/debug/stable

### エラーメッセージ
```
[完全なエラーメッセージ]
```

### 試行した解決法
1. 
2. 

### 最終的な解決
```lean
-- 解決コード
```

### 学習事項
- 
```

---

このカタログは継続的に更新され、プロジェクトの全エラー知識を集約します。
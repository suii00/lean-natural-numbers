# Mathlib4 Import発見ガイド - 実戦的方法論

## 🎯 問題の本質

**Mathlibは急速に進化する巨大なライブラリ**であり、モジュールの場所とAPI名が頻繁に変更されます。これは形式数学学習者にとって最大の障壁の一つです。

## 📊 我々が直面したImport問題の実例

### Category 1: モジュール再編成エラー
```lean
❌ import Mathlib.RingTheory.PrimeSpectrum
✅ import Mathlib.RingTheory.Spectrum.Prime.Basic

❌ import Mathlib.GroupTheory.QuotientGroup  
✅ import Mathlib.GroupTheory.QuotientGroup.Basic

❌ import Mathlib.GroupTheory.Subgroup.Lattice
✅ import Mathlib.Algebra.Group.Subgroup.Lattice

❌ import Mathlib.RingTheory.Ideal.Quotient
✅ import Mathlib.RingTheory.Ideal.Quotient.Basic

❌ import Mathlib.Topology.CompactOpen
✅ import Mathlib.Topology.Compactness.Compact
```

### Category 2: 予想外の場所への移動
```lean
❌ import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
✅ import Mathlib.RingTheory.Spectrum.Prime.Basic  # 実際はRingTheory配下

❌ import Mathlib.RingTheory.Ideal.Quotient
✅ import Mathlib.RingTheory.Ideal.Quotient.Basic  # .Basic サフィックス必要
```

---

## 🔧 体系的Import発見手法

### Method 1: ファイルシステム直接探索
```powershell
# PowerShell/Bash
find "C:\path\to\mathlib\Mathlib" -name "*PrimeSpectrum*" -type f
ls "C:\path\to\mathlib\Mathlib" | grep -r "Prime"
```

**利点**: 確実、リアルタイム情報
**欠点**: 時間がかかる

### Method 2: Lean内での試行錯誤
```lean
-- 段階的試行
#check PrimeSpectrum  -- エラーメッセージから手がかり取得
import Mathlib.RingTheory.Spectrum.Prime.Defs  -- 基本から試行
#check PrimeSpectrum.asIdeal  -- より具体的な機能を確認
```

### Method 3: 関連概念からの逆引き
```lean
-- 知っている関連概念から辿る
#check Ideal.IsPrime  -- → RingTheory.Ideal.Prime
#check TopologicalSpace  -- → Topology.Basic
#check CompactSpace  -- → Topology.Compactness.Compact
```

### Method 4: GitHubのMathlib検索
```
site:github.com/leanprover-community/mathlib4 "def PrimeSpectrum"
site:github.com/leanprover-community/mathlib4 "basicOpen"
```

---

## 🏗️ Mathlib4のモジュール構造パターン

### Pattern 1: 階層的細分化
```
Old: Mathlib.RingTheory.PrimeSpectrum
New: Mathlib.RingTheory.Spectrum.Prime.{Defs, Basic, Topology}
```

### Pattern 2: 基本/操作分離
```
Mathlib.GroupTheory.QuotientGroup.Basic     # 基本定義
Mathlib.GroupTheory.QuotientGroup.Operations # 操作
```

### Pattern 3: 分野横断的再編成
```
Old: Mathlib.GroupTheory.Subgroup.Lattice
New: Mathlib.Algebra.Group.Subgroup.Lattice  # Algebra配下に統合
```

### Pattern 4: 位相/幾何学の統合
```
Mathlib.Topology.Compactness.Compact  # 位相論
Mathlib.AlgebraicGeometry.Scheme       # 代数幾何
```

---

## 🎯 分野別Import発見戦略

### Ring Theory (環論)
```lean
-- 基本構造
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations

-- 商とホモロジー
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

-- スペクトラム
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
```

### Group Theory (群論)
```lean
-- 基本群論
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

-- 商群
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Hom

-- 格子
import Mathlib.Algebra.Group.Subgroup.Lattice
```

### Topology (位相論)  
```lean
-- 基本位相
import Mathlib.Topology.Basic

-- コンパクト性
import Mathlib.Topology.Compactness.Compact

-- 構成可能集合
import Mathlib.Topology.Constructible
```

### Algebraic Geometry (代数幾何)
```lean
-- スキーム
import Mathlib.AlgebraicGeometry.Scheme

-- 射影スペクトラム  
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

-- 構造層
import Mathlib.AlgebraicGeometry.StructureSheaf
```

---

## 📈 Import発見の効率化テクニック

### Technique 1: 段階的Import構築
```lean
-- Step 1: 最小限から始める
import Mathlib.RingTheory.Ideal.Basic

-- Step 2: 必要に応じて追加
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic

-- Step 3: エラーメッセージに従って調整
```

### Technique 2: Import テンプレート作成
```lean
-- Ring Theory Template
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Spectrum.Prime.Basic
```

### Technique 3: API探索セクション
```lean
section APIExploration
#check PrimeSpectrum
#check PrimeSpectrum.asIdeal
#check PrimeSpectrum.basicOpen
#check zeroLocus
end APIExploration
```

---

## 🚨 よくある落とし穴と対策

### 落とし穴1: 古いドキュメントの情報
**問題**: Web上の情報が古いMathlib3時代のもの
**対策**: 必ず最新のGitHubソースを確認

### 落とし穴2: 似た名前の別モジュール
**問題**: `PrimeSpectrum` vs `ProjectiveSpectrum`
**対策**: 正確な概念名で検索

### 落とし穴3: 循環import
**問題**: 複数のモジュールを同時にimportして循環参照
**対策**: 最小限必要なもののみimport

### 落とし穴4: 名前空間の混乱
**問題**: 同名の定義が複数の場所に存在
**対策**: 明示的な名前空間指定

---

## 🏆 ベストプラクティス

### 1. Import組織化原則
```lean
-- 分野別にグループ化
-- 基本 → 高度の順序
-- コメントで目的を明記

-- Ring Theory Fundamentals
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Prime

-- Spectrum Theory  
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

-- Algebraic Geometry Applications
import Mathlib.AlgebraicGeometry.Scheme
```

### 2. Import発見の記録
```lean
-- 成功したImportパターンをコメントで記録
-- import Mathlib.RingTheory.Spectrum.Prime.Basic  -- 2025-08-21 verified working
-- この情報は将来の自分や他の学習者に価値
```

### 3. エラードリブンImport改善
```lean
-- エラーメッセージを注意深く読む
-- 提案されたImportを試す
-- 最小限のImportセットを維持
```

---

## 📚 学習リソースと参考情報

### 公式リソース
1. **Mathlib4 Documentation**: https://leanprover-community.github.io/mathlib4_docs/
2. **GitHub Source**: https://github.com/leanprover-community/mathlib4
3. **Lean Community Forum**: https://leanprover.zulipchat.com/

### 非公式だが有用
1. **Mathlib検索エンジン**: https://loogle.lean-lang.org/
2. **API Browser**: https://leanprover-community.github.io/mathlib_docs/
3. **Stack Overflow**: lean4 + mathlib タグ

---

## 🎯 結論とメタ学習

### 重要な認識
**Mathlibの急速な変化は「バグ」ではなく「特徴」である。**

活発な開発コミュニティによる継続的な改善の結果として、より良い組織化と機能性を追求している。

### 学習者への推奨
1. **変化を受け入れる**: Importエラーは学習機会
2. **体系的アプローチ**: 試行錯誤ではなく方法論的探索
3. **記録の習慣**: 成功パターンの文書化
4. **コミュニティ活用**: 詰まったら積極的に質問

### 形式数学の未来
Import発見の困難さは、形式数学が「生きている分野」である証拠。この困難を乗り越える過程で、より深い数学的理解と技術的習熟を獲得できる。

---

*Mathlib Import Discovery Guide完成: 2025-08-21*  
*対象: Mathlib4の急速な変化への対応*  
*方法論: 体系的Import発見戦略*  
*目標: 効率的な形式数学学習環境の確立*

**🏛️ ブルバキ精神の現代的適用: 変化する環境での構造的思考 🏛️**
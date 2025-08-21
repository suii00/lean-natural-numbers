# Mathlib4 Import クイックリファレンス

## 🚀 緊急時Import早見表

**Mathlibの変化が激しい問題への即効対応カード**

---

## ⚡ 最頻出Import（99%成功）

### Ring Theory必須セット
```lean
import Mathlib.RingTheory.Ideal.Basic          -- Ideal基本
import Mathlib.RingTheory.Ideal.Operations     -- map, comap等
import Mathlib.RingTheory.Ideal.Prime          -- IsPrime
```

### Group Theory必須セット  
```lean
import Mathlib.GroupTheory.QuotientGroup.Basic -- 商群基本
import Mathlib.Algebra.Group.Subgroup.Basic    -- 部分群基本
```

### Topology必須セット
```lean
import Mathlib.Topology.Basic                  -- TopologicalSpace
import Mathlib.Topology.Compactness.Compact   -- CompactSpace
```

---

## 🎯 専門分野別クイックImport

### 素スペクトラム・代数幾何
```lean
import Mathlib.RingTheory.Spectrum.Prime.Defs      -- PrimeSpectrum型
import Mathlib.RingTheory.Spectrum.Prime.Basic     -- 基本性質  
import Mathlib.RingTheory.Spectrum.Prime.Topology  -- Zariski位相
```

### 同型定理・群論
```lean
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Hom  
import Mathlib.Algebra.Group.Subgroup.Lattice
```

### イデアル・環論
```lean
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Submodule.Map  -- mem_map代用
```

---

## ❌ ✅ 間違いやすいパターン

| ❌ よくある間違い | ✅ 正しいImport |
|-------------------|-----------------|
| `Mathlib.RingTheory.PrimeSpectrum` | `Mathlib.RingTheory.Spectrum.Prime.Basic` |
| `Mathlib.GroupTheory.QuotientGroup` | `Mathlib.GroupTheory.QuotientGroup.Basic` |  
| `Mathlib.GroupTheory.Subgroup.Lattice` | `Mathlib.Algebra.Group.Subgroup.Lattice` |
| `Mathlib.RingTheory.Ideal.Quotient` | `Mathlib.RingTheory.Ideal.Quotient.Basic` |
| `Mathlib.Topology.CompactOpen` | `Mathlib.Topology.Compactness.Compact` |

---

## 🔧 緊急時デバッグ手順

### Step 1: エラーメッセージ確認
```
error: object file '.../.../XXX.olean' does not exist
→ モジュールパスが間違っている
```

### Step 2: ファイルシステム検索
```bash
find mathlib -name "*PrimeSpectrum*" -type f
```

### Step 3: 段階的構築
```lean
-- 最小限から開始
import Mathlib.RingTheory.Ideal.Basic
#check Ideal  -- 成功確認

-- 段階的追加
import Mathlib.RingTheory.Spectrum.Prime.Basic  
#check PrimeSpectrum  -- 成功確認
```

---

## 📊 成功率ランキング

### Tier S（成功率95%+）
- `Mathlib.RingTheory.Ideal.Basic`
- `Mathlib.Topology.Basic`  
- `Mathlib.GroupTheory.QuotientGroup.Basic`

### Tier A（成功率80-95%）
- `Mathlib.RingTheory.Spectrum.Prime.Basic`
- `Mathlib.Algebra.Group.Subgroup.Lattice`
- `Mathlib.Topology.Compactness.Compact`

### Tier B（成功率60-80%、要注意）
- 高度な代数幾何関連
- 複雑な位相論
- ホモロジー代数

---

## ⚡ API名変更クイックガイド

| 旧API | 新API |
|-------|-------|
| `mem_ker` | `MonoidHom.mem_ker` |
| `eq_one_iff_mem` | `QuotientGroup.eq_one_iff` |
| `lift_mk'` | `QuotientGroup.lift_mk` |
| `mul_mem_left` | `Ideal.mul_mem_left` |

---

## 🆘 詰まった時の最終手段

### 1. GitHub直接検索
```
site:github.com/leanprover-community/mathlib4 "def PrimeSpectrum"
```

### 2. Zulipコミュニティ質問
- URL: https://leanprover.zulipchat.com/
- Stream: #mathlib
- 具体的なエラーメッセージを添付

### 3. 関連概念からの逆引き
```lean
#check Ideal.IsPrime  -- 成功 → RingTheory.Ideal.* 系統
-- → PrimeSpectrumも同じディレクトリの可能性
```

---

## 🏆 プロTips

### Tip 1: Import最小化
必要最小限のImportで開始、エラーに応じて追加

### Tip 2: 記録の習慣  
成功したImportパターンは即座に記録

### Tip 3: 分野別テンプレート化
よく使う組み合わせをテンプレート保存

### Tip 4: 定期的な検証
Mathlibアップデート時は全Importを再確認

---

**緊急時はこのカードを参照して時間節約！**

*Quick Reference Card 作成: 2025-08-21*  
*対象: Mathlib4 急速変化対応*  
*目的: Import発見時間の劇的短縮*
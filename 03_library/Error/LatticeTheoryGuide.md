# Lean 4 格子理論ガイド：Ideal型での格子演算

## 📚 基本概念

### SemilatticeSup（上半束）の定義
```lean
class SemilatticeSup (α : Type u) extends PartialOrder α where
  sup : α → α → α  -- 二項上限（結び、⊔）
  protected le_sup_left : ∀ a b : α, a ≤ sup a b   -- 左側は上限以下
  protected le_sup_right : ∀ a b : α, b ≤ sup a b  -- 右側は上限以下
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → sup a b ≤ c  -- 最小上界性
```

### SemilatticeInf（下半束）の定義
```lean
class SemilatticeInf (α : Type u) extends PartialOrder α where
  inf : α → α → α  -- 二項下限（交わり、⊓）
  protected inf_le_left : ∀ a b : α, inf a b ≤ a   -- 下限は左側以下
  protected inf_le_right : ∀ a b : α, inf a b ≤ b  -- 下限は右側以下
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ inf b c  -- 最大下界性
```

---

## 🎯 Ideal型での格子演算

### 重要な事実
`Ideal R`は自動的に以下のインスタンスを持つ：
- `PartialOrder (Ideal R)` - 包含関係による順序
- `SemilatticeSup (Ideal R)` - イデアルの和 `I ⊔ J`
- `SemilatticeInf (Ideal R)` - イデアルの交わり `I ⊓ J`
- `CompleteLattice (Ideal R)` - 完備束構造

### 必要なimport
```lean
import Mathlib.RingTheory.Ideal.Operations  -- 基本的なイデアル演算
import Mathlib.RingTheory.Ideal.Quotient.Basic  -- 商環関連
```

---

## 🔧 利用可能な補題

### 基本的な格子演算の補題

| 補題名 | 型 | 説明 |
|--------|-----|------|
| `sup_comm` | `a ⊔ b = b ⊔ a` | 結びの可換性 |
| `inf_comm` | `a ⊓ b = b ⊓ a` | 交わりの可換性 |
| `sup_assoc` | `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)` | 結びの結合性 |
| `inf_assoc` | `(a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)` | 交わりの結合性 |
| `sup_idem` | `a ⊔ a = a` | 結びの冪等性 |
| `inf_idem` | `a ⊓ a = a` | 交わりの冪等性 |

### 特殊元との演算

| 補題名 | 型 | 説明 |
|--------|-----|------|
| `sup_bot_eq` | `a ⊔ ⊥ = a` | 最小元との結び |
| `inf_bot_eq` | `a ⊓ ⊥ = ⊥` | 最小元との交わり |
| `sup_top_eq` | `a ⊔ ⊤ = ⊤` | 最大元との結び |
| `inf_top_eq` | `a ⊓ ⊤ = a` | 最大元との交わり |

### 順序関係の補題

| 補題名 | 型 | 説明 |
|--------|-----|------|
| `le_sup_left` | `a ≤ a ⊔ b` | 左側は結び以下 |
| `le_sup_right` | `b ≤ a ⊔ b` | 右側は結び以下 |
| `inf_le_left` | `a ⊓ b ≤ a` | 交わりは左側以下 |
| `inf_le_right` | `a ⊓ b ≤ b` | 交わりは右側以下 |
| `sup_le` | `a ≤ c → b ≤ c → a ⊔ b ≤ c` | 上界の普遍性 |
| `le_inf` | `c ≤ a → c ≤ b → c ≤ a ⊓ b` | 下界の普遍性 |

---

## 💡 実装例

### 例1: イデアルの和の可換性
```lean
import Mathlib.RingTheory.Ideal.Operations

variable {R : Type*} [CommRing R]

example (I J : Ideal R) : I ⊔ J = J ⊔ I := by
  exact sup_comm  -- 自動的にSemilatticeSupインスタンスが使われる
```

### 例2: モジュラー法則の証明（簡略版）
```lean
theorem modular_law_simple (I J K : Ideal R) (h : I ≤ K) :
  I ⊔ (J ⊓ K) = (I ⊔ J) ⊓ K := by
  apply le_antisymm
  · -- I ⊔ (J ⊓ K) ≤ (I ⊔ J) ⊓ K
    apply sup_le
    · exact le_inf le_sup_left h
    · exact le_inf (inf_le_left.trans le_sup_right) inf_le_right
  · -- (I ⊔ J) ⊓ K ≤ I ⊔ (J ⊓ K)
    -- この方向はより複雑
    sorry
```

### 例3: 分配的性質（弱版）
```lean
theorem weak_distributivity (I J K : Ideal R) :
  (I ⊓ J) ⊔ (I ⊓ K) ≤ I ⊓ (J ⊔ K) := by
  apply le_inf
  · apply sup_le <;> exact inf_le_left
  · apply sup_le
    · exact inf_le_right.trans le_sup_left
    · exact inf_le_right.trans le_sup_right
```

---

## ⚠️ よくある間違いと対処法

### 間違い1: 型クラスインスタンスエラー
```lean
-- ❌ エラーが出る
theorem test (I J : Ideal R) : I ⊔ J = J ⊔ I := by
  exact sup_comm  -- SemilatticeSupインスタンスが見つからない
```

**解決策**: 正しいimportを追加
```lean
-- ✅ 正しい
import Mathlib.RingTheory.Ideal.Operations

theorem test (I J : Ideal R) : I ⊔ J = J ⊔ I := by
  exact sup_comm
```

### 間違い2: 補題名の混同
```lean
-- ❌ 存在しない補題
apply sup_mono  -- この名前では存在しない
```

**解決策**: 手動で証明
```lean
-- ✅ 正しい
apply sup_le
· exact h1.trans le_sup_left
· exact h2.trans le_sup_right
```

### 間違い3: rflの誤用
```lean
-- ❌ rflは使えない（定義的に等しくない）
theorem test : I ⊔ J = J ⊔ I := by rfl
```

**解決策**: 適切な補題を使用
```lean
-- ✅ 正しい
theorem test : I ⊔ J = J ⊔ I := by exact sup_comm
```

---

## 📖 参考資料

### Mathlibドキュメント
- [Order.Lattice](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Lattice.html)
- [RingTheory.Ideal.Operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)

### 主要な型クラス階層
```
PartialOrder
    ↓
SemilatticeSup  SemilatticeInf
    ↘         ↙
      Lattice
        ↓
  DistribLattice
        ↓
  CompleteLattice
```

---

## 🎯 チートシート

```lean
-- 必須import
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic

-- 基本パターン
variable {R : Type*} [CommRing R]

-- よく使う補題
#check sup_comm      -- a ⊔ b = b ⊔ a
#check inf_comm      -- a ⊓ b = b ⊓ a
#check sup_le        -- a ≤ c → b ≤ c → a ⊔ b ≤ c
#check le_inf        -- c ≤ a → c ≤ b → c ≤ a ⊓ b
#check le_sup_left   -- a ≤ a ⊔ b
#check inf_le_right  -- a ⊓ b ≤ b
```
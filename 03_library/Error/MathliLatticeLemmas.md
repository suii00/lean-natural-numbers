# Mathlib.Order.Lattice 主要補題リファレンス

## 📚 型クラス階層

```
Preorder
    ↓
PartialOrder
    ↓
SemilatticeSup    SemilatticeInf
    ↘                ↙
         Lattice
            ↓
      DistribLattice
            ↓
      LinearOrder
```

## 🎯 SemilatticeSup の主要補題

### 基本性質
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `le_sup_left` | `∀ a b, a ≤ a ⊔ b` | 左要素は上限以下 |
| `le_sup_right` | `∀ a b, b ≤ a ⊔ b` | 右要素は上限以下 |
| `sup_le` | `∀ a b c, a ≤ c → b ≤ c → a ⊔ b ≤ c` | 最小上界性 |
| `sup_le_iff` | `a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c` | 上界の特徴付け |

### 代数的性質
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `sup_comm` | `a ⊔ b = b ⊔ a` | 可換性 |
| `sup_assoc` | `(a ⊔ b) ⊔ c = a ⊔ (b ⊔ c)` | 結合性 |
| `sup_idem` | `a ⊔ a = a` | 冪等性 |

### 順序との相互作用
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `sup_eq_left` | `a ⊔ b = a ↔ b ≤ a` | 左吸収条件 |
| `sup_eq_right` | `a ⊔ b = b ↔ a ≤ b` | 右吸収条件 |
| `left_eq_sup` | `a = a ⊔ b ↔ b ≤ a` | 逆向き左吸収 |
| `right_eq_sup` | `b = a ⊔ b ↔ a ≤ b` | 逆向き右吸収 |

## 🎯 SemilatticeInf の主要補題

### 基本性質
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `inf_le_left` | `∀ a b, a ⊓ b ≤ a` | 下限は左要素以下 |
| `inf_le_right` | `∀ a b, a ⊓ b ≤ b` | 下限は右要素以下 |
| `le_inf` | `∀ a b c, a ≤ b → a ≤ c → a ≤ b ⊓ c` | 最大下界性 |
| `le_inf_iff` | `a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c` | 下界の特徴付け |

### 代数的性質
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `inf_comm` | `a ⊓ b = b ⊓ a` | 可換性 |
| `inf_assoc` | `(a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)` | 結合性 |
| `inf_idem` | `a ⊓ a = a` | 冪等性 |

### 順序との相互作用
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `inf_eq_left` | `a ⊓ b = a ↔ a ≤ b` | 左吸収条件 |
| `inf_eq_right` | `a ⊓ b = b ↔ b ≤ a` | 右吸収条件 |
| `left_eq_inf` | `a = a ⊓ b ↔ a ≤ b` | 逆向き左吸収 |
| `right_eq_inf` | `b = a ⊓ b ↔ b ≤ a` | 逆向き右吸収 |

## 🎯 Lattice の主要補題

### 吸収法則
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `sup_inf_self` | `a ⊔ (a ⊓ b) = a` | 上からの吸収 |
| `inf_sup_self` | `a ⊓ (a ⊔ b) = a` | 下からの吸収 |
| `sup_inf_left` | `(a ⊔ b) ⊓ a = a` | 左吸収 |
| `inf_sup_left` | `(a ⊓ b) ⊔ a = a` | 左吸収（双対） |

### モジュラー不等式
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `inf_le_sup` | `a ⊓ b ≤ a ⊔ b` | 下限は上限以下 |
| `le_sup_inf` | `(a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ (b ⊓ c)` | 弱分配性 |
| `inf_sup_le` | `(a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)` | 双対弱分配性 |

## 🎯 特殊元との演算

### OrderBot（最小元を持つ）
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `bot_le` | `⊥ ≤ a` | 最小元の性質 |
| `sup_bot_eq` | `a ⊔ ⊥ = a` | 最小元との結び |
| `bot_sup_eq` | `⊥ ⊔ a = a` | 可換版 |
| `inf_bot_eq` | `a ⊓ ⊥ = ⊥` | 最小元との交わり |
| `bot_inf_eq` | `⊥ ⊓ a = ⊥` | 可換版 |

### OrderTop（最大元を持つ）
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `le_top` | `a ≤ ⊤` | 最大元の性質 |
| `sup_top_eq` | `a ⊔ ⊤ = ⊤` | 最大元との結び |
| `top_sup_eq` | `⊤ ⊔ a = ⊤` | 可換版 |
| `inf_top_eq` | `a ⊓ ⊤ = a` | 最大元との交わり |
| `top_inf_eq` | `⊤ ⊓ a = a` | 可換版 |

## 🎯 単調性の補題

### 単調性
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `sup_le_sup` | `a ≤ b → c ≤ d → a ⊔ c ≤ b ⊔ d` | 結びの単調性 |
| `inf_le_inf` | `a ≤ b → c ≤ d → a ⊓ c ≤ b ⊓ d` | 交わりの単調性 |
| `sup_le_sup_left` | `a ≤ b → c ⊔ a ≤ c ⊔ b` | 左固定単調性 |
| `sup_le_sup_right` | `a ≤ b → a ⊔ c ≤ b ⊔ c` | 右固定単調性 |
| `inf_le_inf_left` | `a ≤ b → c ⊓ a ≤ c ⊓ b` | 左固定単調性 |
| `inf_le_inf_right` | `a ≤ b → a ⊓ c ≤ b ⊓ c` | 右固定単調性 |

## 🎯 DistribLattice の追加補題

### 分配法則
| 補題名 | 宣言 | 説明 |
|--------|------|------|
| `le_sup_inf` | `(a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ (b ⊓ c)` | 分配不等式 |
| `sup_inf_le` | `(a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)` | 双対分配不等式 |
| `inf_sup_self` | `a ⊓ (a ⊔ b) = a` | 吸収法則 |
| `sup_inf_self` | `a ⊔ (a ⊓ b) = a` | 双対吸収法則 |

## 💡 実用的なパターン

### パターン1: 等式の証明
```lean
-- 両方向の不等式を示す
apply le_antisymm
· -- 左から右への不等式
  apply sup_le
  · exact h1
  · exact h2
· -- 右から左への不等式
  exact le_sup_left
```

### パターン2: モジュラー法則の使用
```lean
-- I ≤ K の条件下で
theorem modular (I J K : α) (h : I ≤ K) :
  I ⊔ (J ⊓ K) = (I ⊔ J) ⊓ K := by
  -- この等式は一般には成立しないが、
  -- h : I ≤ K の条件下では成立する
  sorry
```

### パターン3: 分配性の確認
```lean
-- 分配束でない場合は不等式のみ
example (a b c : α) : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  apply le_inf
  · apply sup_le <;> exact inf_le_left
  · apply sup_le
    · exact inf_le_right.trans le_sup_left
    · exact inf_le_right.trans le_sup_right
```

## 📝 注意事項

1. **ImportはMathlibバージョンに依存**
   - 基本: `import Mathlib.Order.Lattice`
   - イデアル用: `import Mathlib.RingTheory.Ideal.Operations`

2. **型クラス推論**
   - `Ideal R`は自動的に`CompleteLattice`のインスタンス
   - 適切なimportがあれば型クラスは自動推論される

3. **名前の一貫性**
   - `sup` = 上限、結び、join、lub
   - `inf` = 下限、交わり、meet、glb
   - `bot` = 最小元、⊥
   - `top` = 最大元、⊤
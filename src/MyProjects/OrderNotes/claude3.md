## 課題3：順序理論

### 数学分野

**ツォルンの補題と選択公理の同値性**

### ブルバキ的アプローチ

順序集合を関係による抽象的構造として定義し、極大元の存在を集合論の深い性質として扱う。選択公理、整列定理、ツォルンの補題の同値性は数学基礎論の核心である。

### Lean言語での定理記述

```
-- 順序関係の定義
class PartialOrder (α : Type*) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

-- 全順序チェーン
def IsChain {α : Type*} [PartialOrder α] (S : Set α) : Prop :=
  ∀ a b ∈ S, a ≤ b ∨ b ≤ a

-- 上界
def IsUpperBound {α : Type*} [PartialOrder α] (S : Set α) (x : α) : Prop :=
  ∀ a ∈ S, a ≤ x

-- 極大元
def IsMaximal {α : Type*} [PartialOrder α] (S : Set α) (x : α) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, x ≤ y → x = y

-- ツォルンの補題
theorem zorns_lemma {α : Type*} [PartialOrder α] (S : Set α)
    (h : ∀ C ⊆ S, IsChain C → ∃ b ∈ S, IsUpperBound C b) :
    ∃ m ∈ S, IsMaximal S m := by
  sorry

```

### 集合論的基盤

- 関係の性質（反射律、推移律、反対称律）
- 写像による順序の保存
- 超限帰納法の原理

### 証明戦略

1. 選択公理を仮定
2. 極大チェーンの存在を示す
3. その上界が極大元であることを証明

### 関連する数学原論の章

- 第1巻第3章「順序構造」
- 第1巻付録「選択公理」

### 現代数学への応用例

関数解析のハーン・バナッハ定理、代数学の極大イデアル
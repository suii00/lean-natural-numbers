import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice

/-!
# 構造塔と抽象解釈：符号抽象化の階層

プログラム静的解析における「符号抽象化」を、
構造塔 (StructureTowerWithMin) として実装した例。

## 計算論的背景：抽象解釈とは

抽象解釈（Abstract Interpretation）は、プログラムの性質を
**完全には計算せず**、**安全な近似**を用いて効率的に検証する手法。

### 精度とコストのトレードオフ

| Level | 抽象値 | 情報量 | 計算コスト | 応用例 |
|-------|--------|--------|------------|--------|
| 0 | ⊤ | ゼロ | O(1) | 初期状態、不明な変数 |
| 1 | -, 0, + | 符号のみ | O(1) | 「x > 0 か？」の判定 |
| 2 | 具体値 | 完全 | O(log n) | 正確な値が必要な場合 |

### minLayer の計算論的意味

`minLayer(α)` = 「抽象値 α を他の値と区別するのに必要な最小精度」

例：
- `minLayer(⊤) = 0`：レベル0で十分（何も区別しない）
- `minLayer(+) = 1`：符号レベルが必要（正であることを区別）
- `minLayer([42]) = 2`：具体値レベルが必要（42 という値を区別）

## 構造塔としての解釈

- **carrier**：抽象値の全体（⊤ ∪ {-, 0, +} ∪ ℤ）
- **Index**：ℕ（精度レベル：0, 1, 2）
- **layer(n)**：精度 n で区別可能な抽象値の集合
- **minLayer**：最小の区別可能精度

### なぜ構造塔になるか

1. **単調性**：より高い精度は、より多くの値を区別可能
   - `layer(0) ⊆ layer(1) ⊆ layer(2)`

2. **被覆性**：すべての抽象値は `layer(2)` に属する

3. **最小性**：`minLayer` は本当に最小
   - ⊤ は level 0 で区別可能（それ以上不要）
   - 符号は level 1 が必要（level 0 では不可）
   - 具体値は level 2 が必要（level 1 では不可）
-/

namespace SignAbstractionTower

/-! ## 基礎定義：抽象値の型 -/

/-- 符号抽象化の抽象値

プログラム変数の可能な抽象表現：
- `top`：任意の値（最も粗い近似）
- `neg`/`zero`/`pos`：符号情報
- `concrete`：具体的な整数値
-/
inductive AbstractValue : Type
  | top : AbstractValue           -- ⊤（任意の値）
  | neg : AbstractValue           -- 負
  | zero : AbstractValue          -- ゼロ
  | pos : AbstractValue           -- 正
  | concrete : ℤ → AbstractValue  -- 具体値
deriving DecidableEq, Repr

open AbstractValue

/-- 抽象値の見やすい文字列表現 -/
instance : ToString AbstractValue where
  toString
    | top => "⊤"
    | neg => "−"
    | zero => "0"
    | pos => "+"
    | concrete n => s!"[{n}]"

/-! ## 精度レベルの定義（minLayer） -/

/-- その値を区別するのに必要な最小精度

**計算論的意味**：
- Level 0：⊤ のみ（何も区別しない、最小コスト）
- Level 1：符号を区別（-, 0, +）
- Level 2：具体的な整数値を区別（最大コスト）

これが構造塔の `minLayer` 関数に対応する。
-/
def precisionLevel : AbstractValue → ℕ
  | top => 0
  | neg => 1
  | zero => 1
  | pos => 1
  | concrete _ => 2

/-! ## 構造塔の定義 -/

/-- ℕ 添字版の簡約 StructureTowerWithMin

CAT2_complete.lean の完全版から、添字を ℕ に限定した簡易版。
教育目的で最小限の定義に絞っている。
-/
structure SimpleTowerWithMin where
  carrier : Type
  layer : ℕ → Set carrier
  covering : ∀ x, ∃ n, x ∈ layer n
  monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x n, x ∈ layer n → minLayer x ≤ n

/-- 一般の rank 関数から構造塔を得る標準構成

**理論的背景**：
RankTower.lean で示されたように、任意の「ランク関数」
ρ : α → ℕ は自然に構造塔を誘導する。

層を `layer(n) = {x | ρ(x) ≤ n}` と定義すれば、
構造塔の公理（被覆性、単調性、最小性）が自動的に満たされる。

この構成により、証明が極めて簡潔になる。
-/
def towerFromRank {α : Type} (ρ : α → ℕ) : SimpleTowerWithMin :=
{ carrier := α
  layer := fun n => {x | ρ x ≤ n}
  covering := by
    intro x; exact ⟨ρ x, by simp⟩
  monotone := by
    intro i j hij x hx; exact le_trans hx hij
  minLayer := ρ
  minLayer_mem := by intro x; simp
  minLayer_minimal := by intro x n hx; simpa using hx }

/-- 符号抽象化の構造塔

`precisionLevel` をランク関数として、`towerFromRank` により構成。
これにより、すべての構造塔の公理が機械的に証明される。
-/
def signAbstractionTower : SimpleTowerWithMin :=
  towerFromRank precisionLevel

/-! ## 基本補題 -/

/-- 層のメンバーシップを特徴付ける基本同値

この補題により、`x ∈ layer(n)` を `precisionLevel x ≤ n` という
算術的条件に帰着できる。
-/
lemma mem_layer_iff (x : AbstractValue) (n : ℕ) :
    x ∈ signAbstractionTower.layer n ↔ precisionLevel x ≤ n := by
  rfl

/-- precisionLevel の明示的な値（計算用） -/
lemma precisionLevel_top : precisionLevel top = 0 := rfl
lemma precisionLevel_neg : precisionLevel neg = 1 := rfl
lemma precisionLevel_zero : precisionLevel zero = 1 := rfl
lemma precisionLevel_pos : precisionLevel pos = 1 := rfl
lemma precisionLevel_concrete (n : ℤ) : precisionLevel (concrete n) = 2 := rfl

/-! ## 具体例：層の構造 -/

/-- 例1：⊤ は最も粗いレベル（level 0）に属する -/
example : top ∈ signAbstractionTower.layer 0 := by
  simp [mem_layer_iff, precisionLevel]

/-- 例2：符号 + は level 1 に属する -/
example : pos ∈ signAbstractionTower.layer 1 := by
  simp [mem_layer_iff, precisionLevel]

/-- 例3：具体値 42 は level 2 に属する -/
example : concrete 42 ∈ signAbstractionTower.layer 2 := by
  simp [mem_layer_iff, precisionLevel]

/-! ## minLayer の具体的な計算 -/

example : signAbstractionTower.minLayer top = 0 := rfl
example : signAbstractionTower.minLayer neg = 1 := rfl
example : signAbstractionTower.minLayer zero = 1 := rfl
example : signAbstractionTower.minLayer pos = 1 := rfl
example : signAbstractionTower.minLayer (concrete 5) = 2 := rfl
example : signAbstractionTower.minLayer (concrete 0) = 2 := rfl
example : signAbstractionTower.minLayer (concrete (-10)) = 2 := rfl

/-! ## 単調性の帰結 -/

/-- Level 0 は Level 1 に含まれる -/
lemma layer0_subset_layer1 :
    signAbstractionTower.layer 0 ⊆ signAbstractionTower.layer 1 := by
  intro x hx
  exact signAbstractionTower.monotone (by decide : 0 ≤ 1) hx

/-- Level 1 は Level 2 に含まれる -/
lemma layer1_subset_layer2 :
    signAbstractionTower.layer 1 ⊆ signAbstractionTower.layer 2 := by
  intro x hx
  exact signAbstractionTower.monotone (by decide : 1 ≤ 2) hx

/-! ## 抽象化関数：精度を落とす変換 -/

/-- 整数から符号抽象値への変換（抽象化）

**プログラム検証での意味**：
具体的な整数値から符号情報への「情報の削減」。
精度を落として計算コストを削減する。

注意：これは構造塔の射ではない（精度が落ちるため）。
-/
def abstractToSign : ℤ → AbstractValue
  | n => if n < 0 then neg else if n = 0 then zero else pos

/-- 抽象化により精度が level 1 になる -/
lemma abstractToSign_precision (n : ℤ) :
    precisionLevel (abstractToSign n) = 1 := by
  by_cases hneg : n < 0
  · simp [abstractToSign, hneg, precisionLevel]
  · by_cases hz : n = 0
    · simp [abstractToSign, hneg, hz, precisionLevel]
    · have hpos : 0 < n := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hz)
      simp [abstractToSign, hneg, hz, hpos.ne', precisionLevel]

/-! ## 判定関数：プログラム検証での使用 -/

/-- 抽象値が正であるかの判定

**戻り値の意味**：
- `some true`：確実に正
- `some false`：確実に非正
- `none`：不明（さらに精度を上げる必要あり）

**プログラム検証での応用**：
```
if (x > 0) { ... } else { ... }
```
このような条件分岐を静的に解析する際に使用。
-/
def isPositive : AbstractValue → Option Bool
  | top => none
  | neg => some false
  | zero => some false
  | pos => some true
  | concrete n => some (n > 0)

/-- 判定関数の具体例 -/
example : isPositive (concrete 5) = some true := by simp [isPositive]
example : isPositive pos = some true := by rfl
example : isPositive neg = some false := by rfl
example : isPositive zero = some false := by rfl
example : isPositive top = none := by rfl

/-! ## 実行可能性の実証（DecidableEq の活用） -/

-- 以下のコマンドで実際に計算可能（インタラクティブに確認）
#eval precisionLevel top                    -- 出力: 0
#eval precisionLevel pos                    -- 出力: 1
#eval precisionLevel (concrete 42)          -- 出力: 2

#eval abstractToSign 5                      -- 出力: pos
#eval abstractToSign 0                      -- 出力: zero
#eval abstractToSign (-3)                   -- 出力: neg

#eval isPositive (concrete 10)              -- 出力: some true
#eval isPositive top                        -- 出力: none

#eval signAbstractionTower.minLayer top     -- 出力: 0
#eval signAbstractionTower.minLayer pos     -- 出力: 1
#eval signAbstractionTower.minLayer (concrete 100)  -- 出力: 2

/-! ## テストスイート -/

namespace Tests

/-- 単調性のテスト -/
example : ∀ (x : AbstractValue) (i j : ℕ), 
    i ≤ j → 
    x ∈ signAbstractionTower.layer i → 
    x ∈ signAbstractionTower.layer j := by
  intro x i j hij hx
  exact signAbstractionTower.monotone hij hx

/-- minLayer の最小性のテスト -/
example : ∀ (x : AbstractValue) (n : ℕ),
    x ∈ signAbstractionTower.layer n →
    signAbstractionTower.minLayer x ≤ n := by
  intro x n hx
  exact signAbstractionTower.minLayer_minimal x n hx

/-- 被覆性のテスト -/
example : ∀ (x : AbstractValue),
    ∃ n, x ∈ signAbstractionTower.layer n := by
  intro x
  exact signAbstractionTower.covering x

/-- 各値での minLayer 計算の正確性 -/
example : signAbstractionTower.minLayer top = 0 := rfl
example : signAbstractionTower.minLayer neg = 1 := rfl
example : signAbstractionTower.minLayer zero = 1 := rfl
example : signAbstractionTower.minLayer pos = 1 := rfl
example : signAbstractionTower.minLayer (concrete 0) = 2 := rfl
example : signAbstractionTower.minLayer (concrete 100) = 2 := rfl
example : signAbstractionTower.minLayer (concrete (-5)) = 2 := rfl

end Tests

/-!
## 学習のまとめ

### この例から学べること

1. **minLayer の計算論的解釈**
   - 「性質を検証するのに必要な最小の解析精度」
   - プログラム検証における実用的な概念

2. **rank 関数のパターン**
   - `towerFromRank` による機械的な構成
   - 証明の簡潔性（ほとんど自明）

3. **決定可能性**
   - `DecidableEq` により `#eval` で実行可能
   - 理論と計算の統合

4. **実用性**
   - 実際のプログラム検証ツール（Astrée など）で使用される技術
   - 精度とコストのトレードオフの明示

### 既存例との違い

- **線形包（Closure_Basic.lean）**：「何個の基底が必要か」（代数的）
- **符号抽象化（本例）**：「どれだけ詳細な解析が必要か」（計算論的）
- **自然数（Bourbaki_Lean_Guide.lean）**：「順序構造そのもの」（順序理論的）

### 一般化への道筋

この枠組みは以下にも適用可能：
- 区間抽象化：`[a, b]` の形での値の近似
- 多面体抽象化：より複雑な制約の組み合わせ
- 型の精度：単純型 → 洗練型 → 依存型
- 形状解析：ポインタの指す先の抽象表現
-/

end SignAbstractionTower

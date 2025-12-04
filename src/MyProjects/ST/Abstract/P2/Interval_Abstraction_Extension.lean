import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic

/-!
# 区間抽象化による構造塔の拡張

符号抽象化（AbstractValue）から区間抽象化（IntervalValue）への拡張。
より実用的なプログラム検証への応用を示す。

## 精度階層の拡張

- Level 0: ⊤（任意の値）
- Level 1: 符号（-, 0, +）
- Level 2: 粗い区間（例：[-10, 10]）
- Level 3: 細かい区間（例：[3, 5]）
- Level 4: 具体値（例：[4, 4]）

## なぜこれが構造塔になるか

より細かい区間は、より粗い区間に含まれる：
[3, 5] ⊆ [-10, 10] ⊆ ℚ

minLayer(x) = 「x を含む最小の区間の精度レベル」
-/

namespace IntervalAbstraction

/-- 有理数の区間を表す型 -/
structure Interval where
  lower : ℚ
  upper : ℚ
  valid : lower ≤ upper

/-- 区間の幅を計算 -/
def Interval.width (i : Interval) : ℚ := i.upper - i.lower

/-- 区間が点（具体値）かどうか -/
def Interval.isPoint (i : Interval) : Bool := i.lower = i.upper

/-- 区間抽象化の抽象値（符号抽象化を拡張） -/
inductive IntervalValue : Type
  | Top : IntervalValue                     -- ⊤（任意の値）
  | SignNeg : IntervalValue                -- 負（符号レベル）
  | SignZero : IntervalValue               -- ゼロ（符号レベル）
  | SignPos : IntervalValue                -- 正（符号レベル）
  | CoarseInterval : Interval → IntervalValue  -- 粗い区間
  | FineInterval : Interval → IntervalValue    -- 細かい区間
  | Point : ℚ → IntervalValue              -- 具体値

open IntervalValue

/-- 区間の「粗さ」を測る閾値 -/
def coarseThreshold : ℚ := 20

/-- 精度レベルの定義（minLayer）

Level 0: ⊤
Level 1: 符号
Level 2: 幅 > 20 の粗い区間
Level 3: 幅 ≤ 20 の細かい区間
Level 4: 点（具体値）
-/
def intervalPrecision : IntervalValue → ℕ
  | Top => 0
  | SignNeg => 1
  | SignZero => 1
  | SignPos => 1
  | CoarseInterval i => if i.width > coarseThreshold then 2 else 3
  | FineInterval i => 3
  | Point _ => 4

/-- 簡約版 StructureTowerWithMin -/
structure SimpleTowerWithMin where
  carrier : Type
  layer : ℕ → Set carrier
  covering : ∀ x, ∃ n, x ∈ layer n
  monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x n, x ∈ layer n → minLayer x ≤ n

/-- rank 関数から構造塔を構成 -/
def towerFromRank {α : Type} (ρ : α → ℕ) : SimpleTowerWithMin :=
{ carrier := α
  layer := fun n => {x | ρ x ≤ n}
  covering := by intro x; exact ⟨ρ x, by simp⟩
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := ρ
  minLayer_mem := by intro x; simp
  minLayer_minimal := by intro x n hx; simpa using hx }

/-- 区間抽象化の構造塔 -/
def intervalTower : SimpleTowerWithMin :=
  towerFromRank intervalPrecision

/-! ## 具体例：プログラム検証での使用 -/

/-- 例1：変数が「正」と分かっている場合（Level 1） -/
example : SignPos ∈ intervalTower.layer 1 := by
  simp [intervalTower, towerFromRank, intervalPrecision]

/-- 例2：変数が区間 [-100, 100] にある場合（Level 2）
これは粗い区間なので、符号判定には使えないが、
オーバーフローチェックには有用 -/
noncomputable example :
    CoarseInterval ⟨-100, 100, by norm_num⟩ ∈ intervalTower.layer 2 := by
  simp [intervalTower, towerFromRank, intervalPrecision,
        Interval.width, coarseThreshold]
  norm_num

/-- 例3：変数が区間 [3, 7] にある場合（Level 3）
細かい区間なので、より詳細な解析が可能 -/
noncomputable example :
    FineInterval ⟨3, 7, by norm_num⟩ ∈ intervalTower.layer 3 := by
  simp [intervalTower, towerFromRank, intervalPrecision]

/-- 例4：変数が正確に 42 の場合（Level 4） -/
example : Point 42 ∈ intervalTower.layer 4 := by
  simp [intervalTower, towerFromRank, intervalPrecision]

/-! ## 抽象化関数：より粗い近似への変換

プログラム検証では、計算コストを削減するために
細かい情報を捨てて粗い近似を使うことがある。

これは構造塔の射として自然に表現される。
-/

/-- 区間から符号への抽象化 -/
def intervalToSign : IntervalValue → IntervalValue
  | Top => Top
  | SignNeg => SignNeg
  | SignZero => SignZero
  | SignPos => SignPos
  | CoarseInterval i =>
      if i.upper < 0 then SignNeg
      else if i.lower > 0 then SignPos
      else Top  -- 符号が不明
  | FineInterval i =>
      if i.upper < 0 then SignNeg
      else if i.lower > 0 then SignPos
      else Top
  | Point p =>
      if p < 0 then SignNeg
      else if p = 0 then SignZero
      else SignPos

/-- 抽象化により精度が下がる（minLayer が減少） -/
lemma intervalToSign_lowers_precision (x : IntervalValue) :
    intervalPrecision (intervalToSign x) ≤ 1 := by
  cases x with
  | Top => simp [intervalToSign, intervalPrecision]
  | SignNeg => simp [intervalToSign, intervalPrecision]
  | SignZero => simp [intervalToSign, intervalPrecision]
  | SignPos => simp [intervalToSign, intervalPrecision]
  | CoarseInterval i =>
      simp [intervalToSign, intervalPrecision]
      split_ifs <;> decide
  | FineInterval i =>
      simp [intervalToSign, intervalPrecision]
      split_ifs <;> decide
  | Point p =>
      simp [intervalToSign, intervalPrecision]
      split_ifs <;> decide

/-! ## 学習のまとめ

この拡張により以下が示される：

1. **階層の拡張性**：
   符号（2レベル）→ 区間（5レベル）への自然な拡張

2. **精度とコストのトレードオフ**：
   | Level | 表現     | 計算コスト | 応用 |
   |-------|----------|------------|------|
   | 0-1   | 符号     | O(1)       | 簡単な判定 |
   | 2-3   | 区間     | O(1)       | 範囲チェック |
   | 4     | 具体値   | O(log n)   | 正確な計算 |

3. **実用性**：
   実際のプログラム検証ツール（例：Astrée）で使用される技術

4. **構造保存**：
   抽象化関数が自然に構造塔の射になる
-/

end IntervalAbstraction

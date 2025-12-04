import Mathlib.Data.Set.Lattice
import Mathlib.Data.Int.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# 区間抽象化による構造塔：完全版

符号抽象化から区間抽象化への拡張に、
区間演算とプログラム解析の実例を追加した完全版。

## 主な拡張

1. **DecidableEq と ToString**：実行可能性とデバッグ性の向上
2. **区間演算**：加法・乗法・包含判定
3. **Widening 演算子**：ループ解析のための不動点計算
4. **実用例**：配列境界チェック

## 精度階層

- Level 0: ⊤（任意の値）
- Level 1: 符号（-, 0, +）
- Level 2: 粗い区間（幅 > 20）
- Level 3: 細かい区間（幅 ≤ 20）
- Level 4: 具体値（点区間）
-/

namespace IntervalAbstraction

/-! ## 基礎定義 -/

/-- 整数の区間を表す型 -/
structure Interval where
  lower : ℤ
  upper : ℤ
  valid : lower ≤ upper
deriving DecidableEq

/-- 区間の見やすい表示 -/
instance : ToString Interval where
  toString i := s!"[{i.lower}, {i.upper}]"

/-- 区間の幅を計算 -/
def Interval.width (i : Interval) : ℤ := i.upper - i.lower

/-- 区間が点（具体値）かどうか -/
def Interval.isPoint (i : Interval) : Bool := i.lower = i.upper

/-! ## 区間演算：抽象解釈の核心 -/

/-- 区間の加法（保守的な近似）

**数学的意味**：
[a, b] + [c, d] = [a+c, b+d]

**プログラム解釈**：
x ∈ [a, b], y ∈ [c, d] ならば、x + y ∈ [a+c, b+d]
-/
def Interval.add (i1 i2 : Interval) : Interval where
  lower := i1.lower + i2.lower
  upper := i1.upper + i2.upper
  valid := by omega

/-- 区間の減法 -/
def Interval.sub (i1 i2 : Interval) : Interval where
  lower := i1.lower - i2.upper
  upper := i1.upper - i2.lower
  valid := by omega

/-- 区間の乗法（4つの端点の min/max）

**数学的意味**：
[a, b] * [c, d] = [min(ac, ad, bc, bd), max(ac, ad, bc, bd)]

負の数を含む場合、符号の組み合わせを考慮する必要がある。
-/
def Interval.mul (i1 i2 : Interval) : Interval where
  lower := min (min (i1.lower * i2.lower) (i1.lower * i2.upper))
              (min (i1.upper * i2.lower) (i1.upper * i2.upper))
  upper := max (max (i1.lower * i2.lower) (i1.lower * i2.upper))
              (max (i1.upper * i2.lower) (i1.upper * i2.upper))
  valid := Int.min_le_max _ _

/-- 区間が具体的な値を含むか -/
def Interval.contains (i : Interval) (n : ℤ) : Bool :=
  i.lower ≤ n ∧ n ≤ i.upper

/-- 区間が他の区間に含まれるか -/
def Interval.subseteq (i1 i2 : Interval) : Bool :=
  i2.lower ≤ i1.lower ∧ i1.upper ≤ i2.upper

/-! ## 区間演算の基本性質 -/

example : 
    let i1 : Interval := ⟨-5, 5, by omega⟩
    let i2 : Interval := ⟨10, 20, by omega⟩
    let i3 := Interval.add i1 i2
    i3.lower = 5 ∧ i3.upper = 25 := by
  simp [Interval.add]

example :
    let i1 : Interval := ⟨2, 3, by omega⟩
    let i2 : Interval := ⟨4, 5, by omega⟩
    let i3 := Interval.mul i1 i2
    i3.lower = 8 ∧ i3.upper = 15 := by
  simp [Interval.mul]

/-! ## Widening 演算子：ループ解析の鍵 -/

/-- Widening 演算子

**目的**：ループの不動点計算を加速する

**原理**：
- 区間が拡大している場合、直ちに「十分大きい」値に跳ぶ
- これにより、有限回の反復で不動点に到達

**例**：
```
x = 0;
while (x < 100) { x = x + 1; }
```

通常：[0,0] → [0,1] → [0,2] → ... → [0,100]（100回反復）
Widening：[0,0] → [0,1] → [0,∞]（2回で安定）
-/
def Interval.widen (i1 i2 : Interval) (threshold : ℤ := 1000) : Interval where
  lower := if i2.lower < i1.lower then -threshold else i1.lower
  upper := if i2.upper > i1.upper then threshold else i1.upper
  valid := by
    split_ifs <;> omega

example :
    let i1 : Interval := ⟨0, 10, by omega⟩
    let i2 : Interval := ⟨0, 15, by omega⟩
    let i3 := Interval.widen i1 i2
    i3.upper = 1000 := by
  simp [Interval.widen]

/-! ## 区間抽象化の抽象値 -/

/-- 区間抽象化の抽象値（符号抽象化を拡張） -/
inductive IntervalValue : Type
  | Top : IntervalValue                     -- ⊤（任意の値）
  | SignNeg : IntervalValue                -- 負（符号レベル）
  | SignZero : IntervalValue               -- ゼロ（符号レベル）
  | SignPos : IntervalValue                -- 正（符号レベル）
  | CoarseInterval : Interval → IntervalValue  -- 粗い区間
  | FineInterval : Interval → IntervalValue    -- 細かい区間
  | Point : ℤ → IntervalValue              -- 具体値
deriving DecidableEq

open IntervalValue

/-- 見やすい文字列表示 -/
instance : ToString IntervalValue where
  toString
    | Top => "⊤"
    | SignNeg => "−"
    | SignZero => "0"
    | SignPos => "+"
    | CoarseInterval i => s!"{i}ᶜᵒᵃʳˢᵉ"
    | FineInterval i => s!"{i}ᶠⁱⁿᵉ"
    | Point p => s!"[{p}]"

/-- 区間の「粗さ」を測る閾値 -/
def coarseThreshold : ℤ := 20

/-- 精度レベルの定義（minLayer） -/
def intervalPrecision : IntervalValue → ℕ
  | IntervalValue.Top => 0
  | IntervalValue.SignNeg => 1
  | IntervalValue.SignZero => 1
  | IntervalValue.SignPos => 1
  | IntervalValue.CoarseInterval i => if i.width > coarseThreshold then 2 else 3
  | IntervalValue.FineInterval _ => 3
  | IntervalValue.Point _ => 4

/-! ## 構造塔の定義 -/

structure SimpleTowerWithMin where
  carrier : Type
  layer : ℕ → Set carrier
  covering : ∀ x, ∃ n, x ∈ layer n
  monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x n, x ∈ layer n → minLayer x ≤ n

def towerFromRank {α : Type} (ρ : α → ℕ) : SimpleTowerWithMin :=
{ carrier := α
  layer := fun n => {x | ρ x ≤ n}
  covering := by intro x; exact ⟨ρ x, by simp⟩
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := ρ
  minLayer_mem := by intro x; simp
  minLayer_minimal := by intro x n hx; simpa using hx }

def intervalTower : SimpleTowerWithMin :=
  towerFromRank intervalPrecision

/-! ## 具体例 -/

example : SignPos ∈ intervalTower.layer 1 := by
  simp [intervalTower, towerFromRank, intervalPrecision]

noncomputable example :
    CoarseInterval ⟨-100, 100, by omega⟩ ∈ intervalTower.layer 2 := by
  simp [intervalTower, towerFromRank, intervalPrecision,
        Interval.width, coarseThreshold]

noncomputable example :
    FineInterval ⟨3, 7, by omega⟩ ∈ intervalTower.layer 3 := by
  simp [intervalTower, towerFromRank, intervalPrecision]

example : Point 42 ∈ intervalTower.layer 4 := by
  simp [intervalTower, towerFromRank, intervalPrecision]

/-! ## 抽象化関数 -/

/-- 区間から符号への抽象化 -/
def intervalToSign : IntervalValue → IntervalValue
  | IntervalValue.Top => IntervalValue.Top
  | IntervalValue.SignNeg => IntervalValue.SignNeg
  | IntervalValue.SignZero => IntervalValue.SignZero
  | IntervalValue.SignPos => IntervalValue.SignPos
  | IntervalValue.CoarseInterval i =>
      if i.upper < 0 then SignNeg
      else if i.lower > 0 then SignPos
      else Top
  | IntervalValue.FineInterval i =>
      if i.upper < 0 then SignNeg
      else if i.lower > 0 then SignPos
      else Top
  | IntervalValue.Point p =>
      if p < 0 then SignNeg
      else if p = 0 then SignZero
      else SignPos

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

/-! ## 実用例：配列境界チェック -/

/-- プログラム状態：変数名 → 区間 -/
def ProgramState := String → Option Interval

/-- 初期状態：i = 0 -/
def initialState : ProgramState :=
  fun var => if var = "i" then some ⟨0, 0, by omega⟩ else none

/-- i = i + 1 の抽象実行 -/
def executeIncrement (state : ProgramState) (var : String) : ProgramState :=
  fun v =>
    if v = var then
      match state v with
      | some i => some (Interval.add i ⟨1, 1, by omega⟩)
      | none => none
    else
      state v

/-- ループ条件 (i < n) による絞り込み -/
def refineByLessThan (state : ProgramState) (var : String) (bound : ℤ) : ProgramState :=
  fun v =>
    if v = var then
      match state v with
      | some i =>
          if i.upper ≥ bound then
            some ⟨i.lower, bound - 1, by omega⟩
          else
            some i
      | none => none
    else
      state v

/-- 配列アクセス arr[i] が安全かチェック -/
def checkArrayAccess (state : ProgramState) (var : String) (arraySize : ℕ) : Bool :=
  match state var with
  | some i => i.lower ≥ 0 ∧ i.upper < arraySize
  | none => false

/-! ## プログラム解析の例

```c
int arr[10];
int i = 0;
while (i < 10) {
  arr[i] = i * 2;  // ← ここが安全か？
  i = i + 1;
}
```

静的解析：
1. 初期状態：i ∈ [0, 0]
2. 条件絞り込み：i ∈ [0, 9]（i < 10 より）
3. 配列アクセス：0 ≤ i < 10 → 安全 ✓
4. インクリメント：i ∈ [1, 10]
5. 次の反復へ...
-/

example :
    let state := initialState
    let refined := refineByLessThan state "i" 10
    let after_increment := executeIncrement refined "i"
    checkArrayAccess refined "i" 10 = true := by
  simp [initialState, refineByLessThan, executeIncrement, 
        checkArrayAccess, Interval.add]

/-! ## 実行可能性の実証 -/

-- 区間演算の実行例
#eval (⟨-5, 5, by omega⟩ : Interval).add ⟨10, 20, by omega⟩
  -- 出力: [5, 25]

#eval (⟨2, 3, by omega⟩ : Interval).mul ⟨4, 5, by omega⟩
  -- 出力: [8, 15]

#eval (⟨0, 10, by omega⟩ : Interval).contains 5
  -- 出力: true

-- 抽象値の精度レベル
#eval intervalPrecision Top                    -- 出力: 0
#eval intervalPrecision SignPos                -- 出力: 1
#eval intervalPrecision (Point 42)             -- 出力: 4

-- 抽象化関数
#eval intervalToSign (Point 5)                 -- 出力: +
#eval intervalToSign (Point (-3))              -- 出力: −
#eval intervalToSign (Point 0)                 -- 出力: 0

-- プログラム解析
#eval checkArrayAccess initialState "i" 10      -- 出力: true

/-!
## 学習のまとめ

### 完全版で追加された機能

1. **区間演算**（add, mul, sub）
   - 抽象解釈の基礎
   - 保守的な近似の実装

2. **Widening 演算子**
   - ループの不動点計算を加速
   - 実用的な静的解析に不可欠

3. **実用例**（配列境界チェック）
   - 具体的なプログラム検証のシナリオ
   - 構造塔理論の実践的応用

4. **実行可能性**
   - `DecidableEq` により `#eval` で計算可能
   - 理論と実装の統合

### 産業ツールとの対応

- **Astrée**：この実装と同じ区間解析 + Widening
- **Polyspace**：区間 + 多面体抽象化
- **Infer**：形状解析 + 区間解析

### 次のステップ

1. Narrowing 演算子（精度回復）
2. 多面体抽象化（より精密）
3. 記号実行との統合
4. 実際のCコード片の完全な解析

この実装は、学術研究と産業応用の橋渡しとなる。
-/

end IntervalAbstraction

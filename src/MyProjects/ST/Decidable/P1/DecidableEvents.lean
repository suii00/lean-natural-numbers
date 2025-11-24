import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

/-!
# 離散確率論の基礎：有限確率空間と Decidable Events

このファイルは、構造塔（Structure Tower）理論の確率論への応用の第一歩である。
ここでは、**有限確率空間**と**decidable な事象**の型レベル定義を提供し、
将来的な DecidableFiltration（離散版フィルトレーション）への橋渡しを行う。

## 数学的背景

確率論において、**事象**（event）とは標本空間の部分集合であり、
**確率**とは事象から [0, 1] への写像である。古典的な確率論では、
無限集合やσ-代数を扱うが、本ファイルでは最も素朴な場合、
すなわち**有限標本空間**のみを対象とする。

有限性は計算可能性をもたらす：
- すべての事象の membership が決定可能（decidable）
- 事象の演算（和・積・補集合）が実際に計算可能
- 確率の計算が有理数演算で実行可能

## このファイルの位置づけ

本ファイルは、以下の階層構造の**第一段階**である：

```
1. DecidableEvents.lean        ← 今回（最も基礎的）
   ↓
2. DecidableAlgebra.lean       （将来）
   ↓
3. DecidableFiltration.lean    （将来：StructureTower のインスタンス）
   ↓
4. ComputableStoppingTime.lean （将来）
   ↓
5. AlgorithmicMartingale.lean  （将来）
```

将来的には、DecidableFiltration は `StructureTowerWithMin` のインスタンスとなり、
- `layer n` = 時刻 n で可観測な事象族
- `minLayer(event)` = その事象が初めて可観測になる時刻

という形で、確率論と構造塔理論が結びつく。

## 主な内容

1. **FiniteSampleSpace**: 有限標本空間の定義
2. **Event**: 事象の型定義（Set Ω + DecidablePred）
3. **基本演算**: 補集合、和、積（すべて decidable）
4. **Decidable インスタンス**: membership, equality, inclusion
5. **基本的な補題**: De Morgan の法則、分配法則など
6. **具体例**: サイコロ、コイン投げ、#eval による計算例

## mathlib との関係

mathlib には一般的な確率論（ProbabilityTheory, MeasureTheory）があるが、
本ファイルはそれとは独立に、**離散版**に特化した定義を提供する。
これにより：
- 計算可能性を最大限に活用
- 学部生にとって理解しやすい定式化
- 構造塔理論との自然な接続

将来的には、離散版と一般版の橋渡し（例：離散測度から一般測度への埋め込み）
も検討される。

## 対象読者

- 学部 3-4 年生レベルの確率論の基礎知識
- Lean 4 の基本的な構文を理解
- 構造塔理論は未学習でも可（将来的な応用を見据える）

## 参考文献

- Williams, David. *Probability with Martingales*. Cambridge University Press, 1991.
- Grimmett & Stirzaker. *Probability and Random Processes*. Oxford University Press, 2001.
- The mathlib Community, *Probability Theory in mathlib*.

-/

/-!
## Part 1: 有限標本空間（Finite Sample Space）

有限標本空間は、確率論における「舞台」である。
有限性により、すべての事象の計算が decidable になる。
-/

/-- 
有限標本空間（Finite Sample Space）

数学的には、標本空間 Ω は以下を持つ型である：
- **有限性**：Ω が有限個の要素からなる（Fintype）
- **識別可能性**：任意の二つの要素の等号判定が可能（DecidableEq）

これらの性質により、事象の membership や演算が decidable になる。

### 例

- サイコロ: Ω = {1, 2, 3, 4, 5, 6} = Fin 6
- コイン投げ: Ω = {H, T} = Bool
- 2個のサイコロ: Ω = Fin 6 × Fin 6

### 教育的注釈

**なぜ Fintype が必要か？**
有限性は計算可能性の源泉である。無限集合では、
「x ∈ A か？」という質問に答えるアルゴリズムが存在しないことがある。
有限集合では、すべての要素を列挙して調べることで、必ず答えが得られる。

**なぜ DecidableEq が必要か？**
等号判定ができないと、集合の membership を調べることができない。
例えば、「x ∈ {y}」を判定するには「x = y か？」を決定する必要がある。
-/
structure FiniteSampleSpace where
  /-- 標本空間の基礎型 -/
  carrier : Type*
  /-- 有限性：carrier が有限個の要素を持つ -/
  [fintype : Fintype carrier]
  /-- 識別可能性：任意の二つの要素の等号判定が可能 -/
  [decidableEq : DecidableEq carrier]

namespace FiniteSampleSpace

/-- Fintype インスタンスを自動的に提供 -/
instance instFintype (Ω : FiniteSampleSpace) : Fintype Ω.carrier :=
  Ω.fintype

/-- DecidableEq インスタンスを自動的に提供 -/
instance instDecidableEq (Ω : FiniteSampleSpace) : DecidableEq Ω.carrier :=
  Ω.decidableEq

/--
標本空間の要素数（cardinality）

有限性があるため、要素数は自然数として計算可能である。
-/
def card (Ω : FiniteSampleSpace) : ℕ :=
  Fintype.card Ω.carrier

/--
標本空間のすべての要素を列挙

有限性により、すべての要素を Finset として取得できる。
これは #eval で実際に計算可能。
-/
def elements (Ω : FiniteSampleSpace) : Finset Ω.carrier :=
  Finset.univ

end FiniteSampleSpace

/-!
## Part 2: 事象（Events）

事象は標本空間の部分集合である。有限標本空間の場合、
すべての事象の membership が decidable である。

### 設計方針

事象の表現には以下の選択肢がある：

**選択肢 1**: `Finset Ω`
- 利点：decidability が組み込み、計算が容易
- 欠点：無限集合への拡張が困難

**選択肢 2**: `Set Ω + DecidablePred`（本実装）
- 利点：mathlib の Set 理論を活用、将来の拡張性
- 欠点：decidability を明示的に証明する必要

本ファイルでは**選択肢 2**を採用する。これにより：
- 無限標本空間への将来的な拡張が容易
- mathlib の Set 理論の豊富な補題を活用可能
- 一般的な確率論への橋渡しがスムーズ

ただし、すべての事象について `DecidablePred` インスタンスを提供し、
実際に計算可能であることを保証する。
-/

/--
事象（Event）の型定義

標本空間 Ω 上の事象は、Ω の部分集合である。

数学的記法：A ⊆ Ω

### 教育的注釈

**なぜ Set を使うか？**
- mathlib の Set 理論は非常に豊富な補題を持つ
- 将来、σ-代数などへ拡張する際に自然
- 和・積・補集合などの演算が標準的

**なぜ Finset ではないか？**
- Finset は計算志向だが、理論展開では Set の方が扱いやすい
- ただし、有限性があるため Set でも計算可能性は保証される
-/
abbrev Event (Ω : Type*) := Set Ω

/--
事象の membership の decidability

有限標本空間 Ω 上の任意の事象 A に対して、
「x ∈ A か？」という問いが decidable であることを保証する型クラス。

これは、事象を**計算可能な述語**として扱うことを意味する。

### 使用例

```lean
variable {Ω : FiniteSampleSpace} (A : Event Ω.carrier) [DecidablePred (· ∈ A)]

#eval if x ∈ A then "yes" else "no"  -- 実際に計算可能
```
-/
class DecidableEvent {Ω : Type*} (A : Event Ω) where
  /-- 事象 A の membership が decidable -/
  mem_decidable : DecidablePred (· ∈ A)

/-- DecidableEvent から DecidablePred インスタンスを提供 -/
instance {Ω : Type*} (A : Event Ω) [h : DecidableEvent A] : 
    DecidablePred (· ∈ A) :=
  h.mem_decidable

/-!
### 教育的注釈：有限性が decidability をもたらすメカニズム

**重要な洞察**：有限標本空間では、「力ずく（brute force）」で
すべての要素を調べることができる。

証明の流れ：
1. Ω は Fintype なので、すべての要素 ω ∈ Ω を列挙できる
2. 各 ω について「ω ∈ A か？」を調べる（DecidableEq を使用）
3. 有限回の判定で結果が得られる

これが、無限集合との本質的な違いである。無限集合では、
すべての要素を調べることができないため、decidability は自明ではない。
-/

namespace Event

variable {Ω : Type*}

/-!
## Part 3: 基本演算（Basic Operations）

事象の基本演算を定義し、すべて decidable であることを示す。
-/

/--
空事象（Empty Event）

数学的には ∅ = {}

「起こり得ない事象」を表す。
確率は P(∅) = 0 である（確率の定義は後のファイルで）。
-/
def empty : Event Ω := ∅

/--
全事象（Universal Event）

数学的には Ω = {ω | ω ∈ Ω}

「必ず起こる事象」を表す。
確率は P(Ω) = 1 である。
-/
def univ : Event Ω := Set.univ

/--
補事象（Complement Event）

数学的には A^c = Ω \ A = {ω ∈ Ω | ω ∉ A}

「A が起こらない」という事象。
De Morgan の法則など、重要な性質を持つ。

### 教育的注釈

complement の decidability：
- A が decidable ⇒ A^c も decidable
- なぜなら「ω ∉ A」は「¬(ω ∈ A)」であり、
  decidable な命題の否定は decidable だから
-/
def complement (A : Event Ω) : Event Ω := Aᶜ

/--
事象の和（Union）

数学的には A ∪ B = {ω | ω ∈ A ∨ ω ∈ B}

「A または B が起こる」という事象。
-/
def union (A B : Event Ω) : Event Ω := A ∪ B

/--
事象の積（Intersection）

数学的には A ∩ B = {ω | ω ∈ A ∧ ω ∈ B}

「A かつ B が起こる」という事象。
-/
def intersection (A B : Event Ω) : Event Ω := A ∩ B

/--
事象の差（Difference）

数学的には A \ B = {ω | ω ∈ A ∧ ω ∉ B}

「A が起こるが B は起こらない」という事象。
-/
def diff (A B : Event Ω) : Event Ω := A \ B

/-!
### Decidability インスタンス

すべての基本演算について、decidability を提供する。
これにより、#eval で実際に計算できることが保証される。
-/

/-- 空事象の membership は常に false -/
instance decidableEmpty : DecidablePred (· ∈ @empty Ω) :=
  fun _ => Decidable.isFalse (Set.not_mem_empty _)

/-- 全事象の membership は常に true -/
instance decidableUniv : DecidablePred (· ∈ @univ Ω) :=
  fun _ => Decidable.isTrue (Set.mem_univ _)

/-- 補事象の decidability -/
instance decidableComplement (A : Event Ω) [DecidablePred (· ∈ A)] :
    DecidablePred (· ∈ complement A) :=
  fun ω => Not.decidable

/-- 和事象の decidability -/
instance decidableUnion (A B : Event Ω) 
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    DecidablePred (· ∈ union A B) :=
  fun ω => Or.decidable

/-- 積事象の decidability -/
instance decidableIntersection (A B : Event Ω)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    DecidablePred (· ∈ intersection A B) :=
  fun ω => And.decidable

/-- 差事象の decidability -/
instance decidableDiff (A B : Event Ω)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    DecidablePred (· ∈ diff A B) :=
  fun ω => And.decidable

/-!
### 事象の包含関係と等号

事象の包含関係（A ⊆ B）と等号（A = B）も decidable である。
-/

/--
事象の包含関係の decidability

有限標本空間では、A ⊆ B かどうかは、
すべての要素 ω ∈ Ω について「ω ∈ A ⇒ ω ∈ B」を調べることで判定できる。
-/
instance decidableSubset [Fintype Ω] [DecidableEq Ω] (A B : Event Ω)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    Decidable (A ⊆ B) :=
  decidable_of_iff 
    (∀ ω ∈ Finset.univ, ω ∈ A → ω ∈ B)
    ⟨fun h ω hω => h ω (Finset.mem_univ ω) hω, 
     fun h ω _ hω => h ω hω⟩

end Event

/-!
## Part 4: 基本的な補題（Basic Lemmas）

事象の演算に関する基本的な性質を補題として提供する。
証明は mathlib の Set 理論の補題を使用するか、sorry で残す。

これらの補題は、decidable であることを型で保証する。
-/

namespace Event

variable {Ω : Type*}

/-!
### De Morgan の法則

古典的な De Morgan の法則：
- (A ∪ B)^c = A^c ∩ B^c
- (A ∩ B)^c = A^c ∪ B^c

証明の方針：Set.ext を使用し、membership の iff を示す。
-/

/-- De Morgan の法則（和の補集合） -/
lemma complement_union (A B : Event Ω) :
    complement (union A B) = intersection (complement A) (complement B) := by
  ext ω
  simp [complement, union, intersection, Set.compl_union]

/-- De Morgan の法則（積の補集合） -/
lemma complement_intersection (A B : Event Ω) :
    complement (intersection A B) = union (complement A) (complement B) := by
  ext ω
  simp [complement, union, intersection, Set.compl_inter]

/-!
### 補集合の性質
-/

/-- 補集合の補集合は元の集合 -/
lemma complement_complement (A : Event Ω) :
    complement (complement A) = A := by
  ext ω
  simp [complement, Set.compl_compl]

/-- 空集合の補集合は全体集合 -/
lemma complement_empty_eq_univ :
    complement (@empty Ω) = univ := by
  ext ω
  simp [complement, empty, univ, Set.compl_empty]

/-- 全体集合の補集合は空集合 -/
lemma complement_univ_eq_empty :
    complement (@univ Ω) = empty := by
  ext ω
  simp [complement, empty, univ, Set.compl_univ]

/-!
### 和と積の性質
-/

/-- 和の可換性 -/
lemma union_comm (A B : Event Ω) :
    union A B = union B A := by
  ext ω
  simp [union, Set.union_comm]

/-- 積の可換性 -/
lemma intersection_comm (A B : Event Ω) :
    intersection A B = intersection B A := by
  ext ω
  simp [intersection, Set.inter_comm]

/-- 和の結合性 -/
lemma union_assoc (A B C : Event Ω) :
    union (union A B) C = union A (union B C) := by
  ext ω
  simp [union, Set.union_assoc]

/-- 積の結合性 -/
lemma intersection_assoc (A B C : Event Ω) :
    intersection (intersection A B) C = intersection A (intersection B C) := by
  ext ω
  simp [intersection, Set.inter_assoc]

/-!
### 分配法則
-/

/-- 積の和に対する分配法則 -/
lemma intersection_union_distrib_left (A B C : Event Ω) :
    intersection A (union B C) = 
      union (intersection A B) (intersection A C) := by
  ext ω
  simp [intersection, union, Set.inter_union_distrib_left]

/-- 和の積に対する分配法則 -/
lemma union_intersection_distrib_left (A B C : Event Ω) :
    union A (intersection B C) = 
      intersection (union A B) (union A C) := by
  ext ω
  simp [union, intersection, Set.union_inter_distrib_left]

end Event

/-!
## Part 5: 具体例（Concrete Examples）

#eval を使った計算可能な例を複数示す。
これにより、理論的な定義が実際に計算できることを確認する。
-/

section Examples

/-!
### 例 1：サイコロの標本空間

6 面サイコロの標本空間を Fin 6 として定義する。
各面は 0, 1, 2, 3, 4, 5 で表される（Lean の Fin 6 は 0-indexed）。

数学的には Ω = {1, 2, 3, 4, 5, 6} だが、
Lean では Fin 6 = {0, 1, 2, 3, 4, 5} として扱う。
-/

/-- サイコロの標本空間（Fin 6 = {0, 1, 2, 3, 4, 5}） -/
def diceSample : FiniteSampleSpace where
  carrier := Fin 6
  fintype := inferInstance
  decidableEq := inferInstance

/--
偶数の目が出る事象

数学的には E = {0, 2, 4} ⊂ Fin 6

### 実装の詳細

述語 `n.val % 2 = 0` を使用して偶数を判定。
Fin 6 の val は 0 から 5 の自然数。
-/
def evenDiceEvent : Event diceSample.carrier :=
  {n : Fin 6 | n.val % 2 = 0}

/-- 偶数事象の decidability -/
instance : DecidablePred (· ∈ evenDiceEvent) :=
  fun n => Nat.decidable_eq (n.val % 2) 0

/-- 具体的な membership のチェック -/
def checkEvenDice (n : Fin 6) : Bool :=
  decide (n ∈ evenDiceEvent)

-- 計算例
#eval checkEvenDice 0  -- true (0 は偶数)
#eval checkEvenDice 1  -- false (1 は奇数)
#eval checkEvenDice 2  -- true (2 は偶数)
#eval checkEvenDice 3  -- false (3 は奇数)
#eval checkEvenDice 4  -- true (4 は偶数)
#eval checkEvenDice 5  -- false (5 は奇数)

/--
奇数の目が出る事象

数学的には O = {1, 3, 5} ⊂ Fin 6

これは偶数事象の補集合である。
-/
def oddDiceEvent : Event diceSample.carrier :=
  Event.complement evenDiceEvent

/-- 奇数事象の decidability（補集合の decidability から自動） -/
instance : DecidablePred (· ∈ oddDiceEvent) :=
  inferInstance

def checkOddDice (n : Fin 6) : Bool :=
  decide (n ∈ oddDiceEvent)

-- 計算例
#eval checkOddDice 0  -- false
#eval checkOddDice 1  -- true
#eval checkOddDice 2  -- false
#eval checkOddDice 3  -- true

/--
大きい目が出る事象（≥ 3）

数学的には B = {3, 4, 5} ⊂ Fin 6
-/
def bigDiceEvent : Event diceSample.carrier :=
  {n : Fin 6 | n.val ≥ 3}

instance : DecidablePred (· ∈ bigDiceEvent) :=
  fun n => Nat.decLe 3 n.val

def checkBigDice (n : Fin 6) : Bool :=
  decide (n ∈ bigDiceEvent)

#eval checkBigDice 2  -- false
#eval checkBigDice 3  -- true
#eval checkBigDice 4  -- true

/--
「偶数かつ大きい」事象

E ∩ B = {4} （0, 2 は小さい；4 だけが偶数かつ大きい）
-/
def evenAndBigEvent : Event diceSample.carrier :=
  Event.intersection evenDiceEvent bigDiceEvent

instance : DecidablePred (· ∈ evenAndBigEvent) :=
  inferInstance

def checkEvenAndBig (n : Fin 6) : Bool :=
  decide (n ∈ evenAndBigEvent)

#eval checkEvenAndBig 0  -- false (偶数だが小さい)
#eval checkEvenAndBig 2  -- false (偶数だが小さい)
#eval checkEvenAndBig 4  -- true  (偶数かつ大きい)
#eval checkEvenAndBig 5  -- false (大きいが奇数)

/-!
### 例 2：コイン投げの標本空間

コイン投げは最もシンプルな確率空間である。
標本空間は Ω = {H, T} = Bool として実装。

- true = 表（Heads）
- false = 裏（Tails）
-/

/-- コイン投げの標本空間（Bool = {true, false}） -/
def coinFlipSample : FiniteSampleSpace where
  carrier := Bool
  fintype := inferInstance
  decidableEq := inferInstance

/-- 表が出る事象（H = {true}） -/
def headsEvent : Event coinFlipSample.carrier :=
  {b : Bool | b = true}

instance : DecidablePred (· ∈ headsEvent) :=
  fun b => Bool.decEq b true

def checkHeads (b : Bool) : Bool :=
  decide (b ∈ headsEvent)

#eval checkHeads true   -- true
#eval checkHeads false  -- false

/-- 裏が出る事象（T = {false}）＝表事象の補集合 -/
def tailsEvent : Event coinFlipSample.carrier :=
  Event.complement headsEvent

instance : DecidablePred (· ∈ tailsEvent) :=
  inferInstance

def checkTails (b : Bool) : Bool :=
  decide (b ∈ tailsEvent)

#eval checkTails true   -- false
#eval checkTails false  -- true

/-!
### 例 3：2個のサイコロの標本空間

2個のサイコロを投げる実験の標本空間は、
Ω = Fin 6 × Fin 6 = {(i, j) | i, j ∈ {0,1,2,3,4,5}}

全部で 6 × 6 = 36 通りの結果がある。
-/

/-- 2個のサイコロの標本空間 -/
def twoDiceSample : FiniteSampleSpace where
  carrier := Fin 6 × Fin 6
  fintype := inferInstance
  decidableEq := inferInstance

/--
「和が 7 になる」事象

Sum7 = {(i, j) | i + j = 7}
    = {(1,6), (2,5), (3,4), (4,3), (5,2), (6,1)}

Fin 6 では {(2,5), (3,4), (4,3), (5,2)} など
（Fin 6 は 0-indexed なので、val で 7 になる組み合わせ）
-/
def sumSevenEvent : Event twoDiceSample.carrier :=
  {p : Fin 6 × Fin 6 | p.1.val + p.2.val = 7}

instance : DecidablePred (· ∈ sumSevenEvent) :=
  fun p => Nat.decidable_eq (p.1.val + p.2.val) 7

def checkSumSeven (p : Fin 6 × Fin 6) : Bool :=
  decide (p ∈ sumSevenEvent)

-- 計算例（Fin 6 は 0-indexed）
#eval checkSumSeven (2, 5)  -- true  (2 + 5 = 7)
#eval checkSumSeven (3, 4)  -- true  (3 + 4 = 7)
#eval checkSumSeven (1, 1)  -- false (1 + 1 = 2)

/-- 「両方とも偶数」事象 -/
def bothEvenEvent : Event twoDiceSample.carrier :=
  {p : Fin 6 × Fin 6 | p.1.val % 2 = 0 ∧ p.2.val % 2 = 0}

instance : DecidablePred (· ∈ bothEvenEvent) :=
  fun p => And.decidable

def checkBothEven (p : Fin 6 × Fin 6) : Bool :=
  decide (p ∈ bothEvenEvent)

#eval checkBothEven (0, 0)  -- true
#eval checkBothEven (2, 4)  -- true
#eval checkBothEven (1, 2)  -- false (1 は奇数)

end Examples

/-!
## Part 6: 構造塔との将来的な接続

このセクションでは、将来のファイル（DecidableFiltration.lean）で
どのように構造塔理論と接続するかを予告する。

### 離散版フィルトレーション（Discrete Filtration）

フィルトレーションとは、時間とともに増加する事象族の系列である：

  ℱ₀ ⊆ ℱ₁ ⊆ ℱ₂ ⊆ ... ⊆ ℱₙ

各 ℱₜ は時刻 t で「可観測な」事象の族。

### 構造塔としての定式化

DecidableFiltration は `StructureTowerWithMin` のインスタンスになる：

```lean
structure DecidableFiltration where
  timeHorizon : ℕ
  sampleSpace : FiniteSampleSpace
  observableAt : ℕ → Set (Event sampleSpace.carrier)
  -- 単調性：時間とともに可観測事象が増える
  monotone : ∀ s t, s ≤ t → observableAt s ⊆ observableAt t
  
instance : StructureTowerWithMin := {
  carrier := Event sampleSpace.carrier
  Index := ℕ
  layer := observableAt
  minLayer := fun A => 
    -- A が初めて可観測になる時刻
    Nat.find (witness that ∃ t, A ∈ observableAt t)
  ...
}
```

### 停止時間との対応

停止時間（stopping time）τ は、
「{τ ≤ t} ∈ ℱₜ」を満たす確率変数である。

構造塔の視点では：
- 事象 {τ ≤ t} の minLayer が ≤ t である
- これは、minLayer 関数による特徴づけそのもの

### 次のステップ

1. **DecidableAlgebra.lean**: 
   Boolean 演算で閉じた事象族（σ-代数の離散版）

2. **DecidableFiltration.lean**: 
   StructureTowerWithMin のインスタンスとしてのフィルトレーション

3. **ComputableStoppingTime.lean**: 
   停止時間の decidable 実装

4. **AlgorithmicMartingale.lean**: 
   有限計算による Optional Stopping Theorem

これらすべてが、本ファイルで定義した decidable events の上に構築される。
-/

/-!
## まとめと学習の指針

### 本ファイルで学んだこと

1. **有限性と計算可能性**
   - Fintype により、すべての事象が decidable になる
   - DecidableEq が membership 判定を可能にする

2. **事象の表現**
   - Set Ω を使用し、DecidablePred で計算可能性を保証
   - 将来の拡張性（無限集合、σ-代数）を確保

3. **基本演算**
   - 補集合、和、積がすべて decidable
   - De Morgan の法則、分配法則などの古典的性質

4. **具体例**
   - サイコロ、コイン投げで理論を実践
   - #eval により実際に計算可能であることを確認

### 次のステップへ

本ファイルは、離散確率論の最も基礎的な層である。
次は以下の方向に進む：

1. **DecidableAlgebra.lean**: 
   Boolean 演算で閉じた事象族
   
2. **確率測度の定義**: 
   Event → ℚ≥0 の写像として確率を導入
   
3. **構造塔への接続**: 
   DecidableFiltration の実装

### 教育的価値

このファイルは、以下を示している：

- **型システムの力**: 計算可能性を型で保証
- **有限性の意義**: 理論と計算の橋渡し
- **段階的構築**: 最も単純な場合から始める重要性

### 参考資料

- `CAT2_complete.lean`: 構造塔の完全な形式化
- `DecidableStructureTower_Examples.lean`: 構造塔の具体例
- mathlib の ProbabilityTheory モジュール（一般論）

-/

/-!
## 演習問題（Exercises）

以下の演習問題は、本ファイルの理解を深めるために設計されている。

### 基礎問題

1. **空事象と全事象**
   - 空事象と全事象が complementary であることを示せ
   - すなわち、`complement empty = univ` を証明せよ

2. **De Morgan の法則の証明**
   - `complement_union` の sorry を埋めよ
   - `complement_intersection` の sorry を埋めよ

3. **分配法則の検証**
   - 具体的な事象で分配法則が成り立つことを #eval で確認せよ

### 応用問題

4. **新しい事象の定義**
   - 「3 で割り切れる目」の事象を定義し、decidability を示せ
   - 「素数の目」の事象を定義し、decidability を示せ

5. **3個のサイコロ**
   - 3個のサイコロの標本空間を定義せよ
   - 「和が 10 になる」事象を定義し、計算可能にせよ

6. **カードデッキ**
   - 52 枚のトランプカード（Fin 52）の標本空間を定義
   - 「スペード」「絵札」などの事象を定義

### 発展問題

7. **事象の族**
   - 事象の列 (Aₙ)ₙ∈ℕ の和集合 ⋃ Aₙ を定義できるか？
   - 有限の場合と無限の場合で何が違うか？

8. **確率の定義**
   - Event → ℚ≥0 の写像として確率を定義するには？
   - どんな公理が必要か？

9. **構造塔への橋渡し**
   - 事象の族がどのように StructureTower の layer になるか考察せよ
   - minLayer 関数はどう定義されるべきか？
-/

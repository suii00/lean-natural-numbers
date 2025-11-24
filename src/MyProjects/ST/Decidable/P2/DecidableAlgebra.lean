import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic
import MyProjects.ST.Decidable.P1.DecidableEvents

open Classical

/-!
# 離散確率論の代数的構造：有限代数と可測性

このファイルは、DecidableEvents.lean の自然な拡張であり、
**有限代数**（finite algebra）の概念を通じて、事象の構造化された族を扱う。

## 数学的背景

測度論において、**σ-代数**（sigma-algebra）は以下を満たす事象族 ℱ である：
1. 全事象を含む：Ω ∈ ℱ
2. 補集合で閉じている：A ∈ ℱ ⇒ Aᶜ ∈ ℱ
3. 可算和で閉じている：(Aₙ) ⊆ ℱ ⇒ ⋃ₙ Aₙ ∈ ℱ

本ファイルでは、有限標本空間における**有限代数**（finite algebra）を扱う：
- 可算和の代わりに、有限和のみを要求
- 有限性により、すべての演算が decidable

## このファイルの位置づけ

```
DecidableEvents.lean      ← 事象の基礎
    ↓
DecidableAlgebra.lean     ← 今回（事象の構造化された族）
    ↓
DecidableFiltration.lean  ← 構造塔のインスタンス化
    ↓
ComputableStoppingTime    ← 停止時間
    ↓
AlgorithmicMartingale     ← マルチンゲール理論
```

## 構造塔理論との接続

**重要な洞察**：有限代数は、構造塔の各層（layer）の構造を記述する。

将来の DecidableFiltration では：
```lean
structure DecidableFiltration where
  ...
  observableAt : ℕ → FiniteAlgebra Ω  -- 各時刻の可観測事象族
  monotone : ∀ s ≤ t, observableAt s ⊆ observableAt t
```

各 `observableAt t` が FiniteAlgebra であることにより：
- 観測された事象の補集合も観測可能
- 観測された事象の和・積も観測可能
- これが「情報の閉包」の数学的表現

## 主な内容

1. **FiniteAlgebra**: 有限代数の定義
2. **基本的な性質**: 積・差で閉じていることなど
3. **具体例**: 自明な代数、全体の代数、生成された代数
4. **可測関数**: 代数間の構造を保存する写像
5. **部分代数**: 代数の包含関係
6. **生成される代数**: 事象族から最小の代数を構成

## 対象読者

- DecidableEvents.lean を理解している
- 学部レベルの集合論・代数学の基礎知識
- 測度論の初歩（σ-代数の定義程度）

## 参考文献

- Billingsley, P. *Probability and Measure*. Wiley, 1995.
- Williams, D. *Probability with Martingales*. Cambridge, 1991.
- Kallenberg, O. *Foundations of Modern Probability*. Springer, 2002.

-/

-- DecidableEvents からの定義を再利用するための準備
-- 実際のプロジェクトでは import を使用

namespace Prob

/-!
## Part 0: DecidableEvents からの必要な定義

実際のプロジェクトでは import を使用。
ここでは自己完結性のため、最小限の定義を再掲。
-/

/-- 有限標本空間（DecidableEvents.lean から） -/
structure FiniteSampleSpace where
  carrier : Type*
  [fintype : Fintype carrier]
  [decidableEq : DecidableEq carrier]

namespace FiniteSampleSpace

instance instFintype (Ω : FiniteSampleSpace) : Fintype Ω.carrier :=
  Ω.fintype

instance instDecidableEq (Ω : FiniteSampleSpace) : DecidableEq Ω.carrier :=
  Ω.decidableEq

end FiniteSampleSpace

/-- 事象の型（DecidableEvents.lean から） -/
abbrev Event (Ω : Type*) := Set Ω

namespace Event

variable {Ω : Type*}

/-- 空事象 -/
def empty : Event Ω := ∅

/-- 全事象 -/
def univ : Event Ω := Set.univ

/-- 補事象 -/
def complement (A : Event Ω) : Event Ω := Aᶜ

/-- 事象の和 -/
def union (A B : Event Ω) : Event Ω := A ∪ B

/-- 事象の積 -/
def intersection (A B : Event Ω) : Event Ω := A ∩ B

/-- 事象の差 -/
def diff (A B : Event Ω) : Event Ω := A \ B

end Event

/-!
## Part 1: 有限代数（Finite Algebra）の定義

有限代数は、Boolean 演算で閉じた事象の族である。
これは σ-代数の有限版であり、以下の性質を持つ：
- 全事象を含む
- 補集合で閉じている
- 有限和で閉じている（または同値に、有限積で閉じている）
-/

/--
有限代数（Finite Algebra）

標本空間 Ω 上の有限代数とは、事象の族 ℱ ⊆ 𝒫(Ω) であって：
1. 全事象を含む：Ω ∈ ℱ
2. 補集合で閉じている：A ∈ ℱ ⇒ Aᶜ ∈ ℱ
3. 有限和で閉じている：A, B ∈ ℱ ⇒ A ∪ B ∈ ℱ

### 教育的注釈

**なぜ「代数」と呼ぶか？**
- 補集合 = 単項演算
- 和・積 = 二項演算
- これらの演算で閉じている = 代数的構造

**σ-代数との違い**
- σ-代数：可算無限個の和で閉じている
- 有限代数：有限個の和のみ
- 有限標本空間では、すべての有限代数はσ-代数

**可測空間**
組 (Ω, ℱ) を可測空間（measurable space）と呼ぶ。
-/
structure FiniteAlgebra (Ω : Type*) where
  /-- 事象の族 -/
  events : Set (Event Ω)
  /-- 空事象を含む（全事象と同値） -/
  has_empty : Event.empty ∈ events
  /-- 補集合で閉じている -/
  closed_complement : ∀ {A : Event Ω}, A ∈ events → Event.complement A ∈ events
  /-- 和で閉じている -/
  closed_union : ∀ {A B : Event Ω}, A ∈ events → B ∈ events →
                 Event.union A B ∈ events

namespace FiniteAlgebra

variable {Ω : Type*}

/-!
### 基本的な性質

有限代数の定義から直ちに従う性質を導出する。
-/

/--
全事象は代数に含まれる

証明：∅ ∈ ℱ かつ補集合で閉じているので、∅ᶜ = Ω ∈ ℱ
-/
theorem has_univ (ℱ : FiniteAlgebra Ω) : Event.univ ∈ ℱ.events := by
  have h := ℱ.closed_complement ℱ.has_empty
  simp [Event.complement, Event.empty, Event.univ] at h ⊢
  exact h

/--
積で閉じている

証明：A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ （De Morgan の法則）
-/
theorem closed_intersection (ℱ : FiniteAlgebra Ω)
    {A B : Event Ω} (hA : A ∈ ℱ.events) (hB : B ∈ ℱ.events) :
    Event.intersection A B ∈ ℱ.events := by
  -- A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ を使用
  have hAc := ℱ.closed_complement hA
  have hBc := ℱ.closed_complement hB
  have hUnion := ℱ.closed_union hAc hBc
  have hComp := ℱ.closed_complement hUnion
  -- (Aᶜ ∪ Bᶜ)ᶜ = A ∩ B を示す
  convert hComp using 1
  ext ω
  simp [Event.complement, Event.union, Event.intersection]

/--
差で閉じている

証明：A \ B = A ∩ Bᶜ
-/
theorem closed_diff (ℱ : FiniteAlgebra Ω)
    {A B : Event Ω} (hA : A ∈ ℱ.events) (hB : B ∈ ℱ.events) :
    Event.diff A B ∈ ℱ.events := by
  have hBc := ℱ.closed_complement hB
  have hInter := ℱ.closed_intersection hA hBc
  -- A \ B = A ∩ Bᶜ
  simpa [Event.diff, Event.intersection, Event.complement] using hInter

/--
有限個の事象の和で閉じている

帰納法により、任意の有限個の事象 A₁, ..., Aₙ ∈ ℱ に対して、
⋃ᵢ Aᵢ ∈ ℱ
-/
theorem closed_finite_union (ℱ : FiniteAlgebra Ω)
    {ι : Type*} [Fintype ι] {A : ι → Event Ω}
    (hA : ∀ i, A i ∈ ℱ.events) :
    (⋃ i, A i) ∈ ℱ.events := by
  classical
  -- Finset.univ を使った帰納法
  sorry  -- 証明の詳細は後で

/--
有限個の事象の積で閉じている
-/
theorem closed_finite_intersection (ℱ : FiniteAlgebra Ω)
    {ι : Type*} [Fintype ι] {A : ι → Event Ω}
    (hA : ∀ i, A i ∈ ℱ.events) :
    (⋂ i, A i) ∈ ℱ.events := by
  -- De Morgan: ⋂ᵢ Aᵢ = (⋃ᵢ Aᵢᶜ)ᶜ
  sorry

/-!
### 代数の包含関係（部分代数）

代数 ℱ が代数 𝒢 の部分代数であるとは、ℱ.events ⊆ 𝒢.events のこと。
-/

/-- 部分代数の関係 -/
def IsSubalgebra (ℱ 𝒢 : FiniteAlgebra Ω) : Prop :=
  ℱ.events ⊆ 𝒢.events

notation:50 ℱ " ⊆ₐ " 𝒢:50 => IsSubalgebra ℱ 𝒢

/-- 部分代数の関係は反射的 -/
theorem subalgebra_refl (ℱ : FiniteAlgebra Ω) : ℱ ⊆ₐ ℱ :=
  Set.Subset.refl _

/-- 部分代数の関係は推移的 -/
theorem subalgebra_trans {ℱ 𝒢 ℋ : FiniteAlgebra Ω}
    (h1 : ℱ ⊆ₐ 𝒢) (h2 : 𝒢 ⊆ₐ ℋ) : ℱ ⊆ₐ ℋ :=
  Set.Subset.trans h1 h2

/-!
## Part 2: 具体的な有限代数の例

いくつかの重要な有限代数の例を構成する。
-/

/--
自明な代数（Trivial Algebra）

ℱ = {∅, Ω} のみを含む最小の代数。

これは、「何も観測できない」状態を表す。
確率論では、時刻 0 の情報（初期状態）に対応。
-/
def trivial : FiniteAlgebra Ω where
  events := {Event.empty, Event.univ}
  has_empty := by simp [Event.empty]
  closed_complement := by
    intro A hA
    simp [Event.complement, Event.empty, Event.univ] at hA ⊢
    cases hA with
    | inl h => right; ext ω; simp [h]
    | inr h => left; ext ω; simp [h]
  closed_union := by
    intro A B hA hB
    simp at hA hB ⊢
    cases hA with
    | inl hA =>
      cases hB with
      | inl hB => left; simp [Event.union, hA, hB]
      | inr hB => right; simp [Event.union, hA, hB, Event.empty, Event.univ]
    | inr hA =>
      right; simp [Event.union, hA, Event.univ]

/--
全体の代数（Power Set Algebra）

ℱ = 𝒫(Ω) すべての事象を含む最大の代数。

これは、「すべてを観測できる」状態を表す。
確率論では、完全な情報に対応。
-/
def powerSet : FiniteAlgebra Ω where
  events := Set.univ
  has_empty := Set.mem_univ _
  closed_complement := fun _ => Set.mem_univ _
  closed_union := fun _ _ => Set.mem_univ _

/-!
### 生成される代数（Generated Algebra）

事象の族 𝒮 が与えられたとき、𝒮 を含む最小の代数 σ(𝒮) を構成できる。

**構成方法**（有限の場合）:
1. 𝒮 のすべての有限和・積・補集合を取る
2. これを有限回繰り返す
3. 有限標本空間では、有限ステップで完了

これは、「𝒮 の事象が観測できるとき、論理的に導出できるすべての事象」を表す。
-/

/--
事象の族から生成される代数

ℱ = σ(𝒮) は、𝒮 を含む最小の代数。

### 実装の注釈

一般的な構成は複雑なので、ここでは存在のみを主張。
具体的な計算例は後で示す。

### 教育的注釈

**生成される代数の重要性**：
- フィルトレーションの定義で中心的役割
- 「観測可能な情報」の形式化
- 停止時間の定義に必要
-/
axiom generated (𝒮 : Set (Event Ω)) : FiniteAlgebra Ω

-- 生成される代数の性質
axiom generated_contains (𝒮 : Set (Event Ω)) : 𝒮 ⊆ (generated 𝒮).events

axiom generated_minimal (𝒮 : Set (Event Ω)) (ℱ : FiniteAlgebra Ω) :
  𝒮 ⊆ ℱ.events → (generated 𝒮) ⊆ₐ ℱ

/-!
### 具体例：サイコロの代数

サイコロの目の偶奇による分割から生成される代数。
-/

section DiceExample

/-- サイコロの標本空間 -/
def diceSample : FiniteSampleSpace where
  carrier := Fin 6
  fintype := inferInstance
  decidableEq := inferInstance

/-- 偶数の目の事象 -/
def evenDice : Event diceSample.carrier :=
  {n : Fin 6 | n.val % 2 = 0}

/-- 偶奇で生成される代数

この代数は以下の 4 つの事象のみを含む：
- ∅（空）
- 偶数の目 = {0, 2, 4}
- 奇数の目 = {1, 3, 5}
- Ω（全体）= {0, 1, 2, 3, 4, 5}

これは、「偶数か奇数か」という情報のみが観測可能な状態を表す。
-/
def evenOddAlgebra : FiniteAlgebra diceSample.carrier where
  events := {
    Event.empty,
    evenDice,
    Event.complement evenDice,
    Event.univ
  }
  has_empty := by simp [Event.empty]
  closed_complement := by
    intro A hA
    simp [Event.complement] at hA ⊢
    cases hA with
    | inl h => sorry  -- ∅ᶜ = Ω
    | inr h =>
      cases h with
      | inl h' => sorry  -- (偶数)ᶜ = 奇数
      | inr h' =>
        cases h' with
        | inl h'' => sorry  -- (奇数)ᶜ = 偶数
        | inr h'' => sorry  -- Ωᶜ = ∅
  closed_union := by
    intro A B hA hB
    sorry  -- 4 × 4 = 16 通りのケース分析

/--
偶奇代数は自明な代数より大きく、全体の代数より小さい
-/
theorem evenOdd_nontrivial :
    trivial ⊆ₐ evenOddAlgebra ∧
    evenOddAlgebra ⊆ₐ powerSet := by
  constructor
  · -- trivial ⊆ evenOddAlgebra
    intro A hA
    simp [trivial, evenOddAlgebra] at hA ⊢
    cases hA with
    | inl h => left; exact h
    | inr h => right; right; right; exact h
  · -- evenOddAlgebra ⊆ powerSet
    intro A hA
    simp [powerSet]

end DiceExample

/-!
## Part 3: 可測関数（Measurable Functions）

代数間の構造を保存する写像を定義する。
これは、「観測可能な情報を保存する関数」の形式化。
-/

/--
可測関数（Measurable Function）

関数 f : Ω → Ω' が (ℱ, 𝒢)-可測であるとは：
∀ B ∈ 𝒢, f⁻¹(B) ∈ ℱ

### 直感的理解

「Ω' で観測可能な事象 B の逆像 f⁻¹(B) が、
 Ω で観測可能である」

### 例

- 恒等関数：常に可測
- 定数関数：常に可測
- ランダム変数：確率空間からℝへの可測関数
-/
structure MeasurableFunction {Ω Ω' : Type*}
    (ℱ : FiniteAlgebra Ω) (𝒢 : FiniteAlgebra Ω') where
  /-- 基礎となる関数 -/
  toFun : Ω → Ω'
  /-- 可測性：すべての 𝒢-可測事象の逆像が ℱ-可測 -/
  measurable : ∀ {B : Event Ω'}, B ∈ 𝒢.events →
               (toFun ⁻¹' B) ∈ ℱ.events

notation:25 ℱ " →ₘ " 𝒢:24 => MeasurableFunction ℱ 𝒢

namespace MeasurableFunction

variable {Ω Ω' Ω'' : Type*}
variable {ℱ : FiniteAlgebra Ω} {𝒢 : FiniteAlgebra Ω'} {ℋ : FiniteAlgebra Ω''}

/-- 恒等可測関数 -/
def id (ℱ : FiniteAlgebra Ω) : ℱ →ₘ ℱ where
  toFun := _root_.id
  measurable := by
    intro B hB
    simp
    exact hB

/-- 可測関数の合成 -/
def comp (g : 𝒢 →ₘ ℋ) (f : ℱ →ₘ 𝒢) : ℱ →ₘ ℋ where
  toFun := g.toFun ∘ f.toFun
  measurable := by
    intro C hC
    simp [Set.preimage_comp]
    have hB := g.measurable hC
    exact f.measurable hB

/-!
Note: 可測関数の像は一般には可測とは限らない（逆像のみ保証）。
-/

end MeasurableFunction

/-!
## Part 4: 構造塔との接続

有限代数が構造塔理論とどう接続するかを予告する。
-/

/-!
### DecidableFiltration への道筋

**フィルトレーション**（filtration）とは、単調増加する代数の系列：

  ℱ₀ ⊆ ℱ₁ ⊆ ℱ₂ ⊆ ... ⊆ ℱₙ

各 ℱₜ は時刻 t で「可観測な事象の族」を表す。

### StructureTowerWithMin のインスタンス化

```lean
structure DecidableFiltration where
  sampleSpace : FiniteSampleSpace
  timeHorizon : ℕ
  observableAt : ℕ → FiniteAlgebra sampleSpace.carrier
  monotone : ∀ s t, s ≤ t → observableAt s ⊆ₐ observableAt t

instance : StructureTowerWithMin where
  carrier := FiniteAlgebra sampleSpace.carrier
  Index := ℕ
  layer := observableAt
  minLayer := fun (ℱ : FiniteAlgebra _) =>
    -- ℱ が初めて observableAt に現れる時刻
    Nat.find (∃ t, ℱ = observableAt t)
  ...
```

### 重要な対応関係

| 構造塔の概念 | フィルトレーションの概念 |
|------------|---------------------|
| carrier    | 代数の全体          |
| Index      | 時刻               |
| layer n    | 時刻 n の可観測代数 |
| minLayer   | 初めて観測可能になる時刻 |
| monotone   | 情報の単調増加      |

### 停止時間との対応

停止時間 τ : Ω → ℕ は、
「∀ t, {τ ≤ t} ∈ ℱₜ」を満たす。

構造塔の言葉では：
- 事象 {τ ≤ t} の minLayer が ≤ t
- これは minLayer 関数による特徴づけそのもの

### 例：コイン投げのフィルトレーション

n 回コイン投げの標本空間 Ω = {H, T}ⁿ に対して：

```
ℱ₀ = {∅, Ω}                    -- 何も観測していない
ℱ₁ = σ(1回目の結果)            -- 1回目まで観測
ℱ₂ = σ(1,2回目の結果)          -- 2回目まで観測
...
ℱₙ = 𝒫(Ω)                      -- すべて観測
```

これは明らかに単調増加：ℱ₀ ⊆ ℱ₁ ⊆ ... ⊆ ℱₙ
-/

/-!
## Part 5: Decidability の保証

有限代数においても、decidability を保証することが重要。
-/

/--
有限代数の membership の decidability

有限標本空間 Ω 上の有限代数 ℱ に対して、
「A ∈ ℱ.events か？」が decidable であるための十分条件。

### 実装の注釈

一般的には、events を Finset として表現することで decidable にできる。
ただし、理論的には Set を使う方が扱いやすい。
-/
class DecidableAlgebra {Ω : Type*} (ℱ : FiniteAlgebra Ω) where
  /-- 代数の membership が decidable -/
  mem_decidable : DecidablePred (· ∈ ℱ.events)

/-- DecidableAlgebra から DecidablePred インスタンスを提供 -/
instance {Ω : Type*} (ℱ : FiniteAlgebra Ω) [h : DecidableAlgebra ℱ] :
    DecidablePred (· ∈ ℱ.events) :=
  h.mem_decidable

/-!
### 具体例の Decidability

自明な代数と全体の代数は decidable：
-/

noncomputable instance trivialDecidable : DecidableAlgebra (trivial : FiniteAlgebra Ω) where
  mem_decidable := by
    intro A
    classical
    change Decidable (A = Event.empty ∨ A = Event.univ)
    infer_instance

noncomputable instance powerSetDecidable [Fintype Ω] :
    DecidableAlgebra (powerSet : FiniteAlgebra Ω) where
  mem_decidable := by
    intro A
    classical
    change Decidable True
    infer_instance

end FiniteAlgebra

end Prob

/-!
## まとめと学習の指針

### 本ファイルで学んだこと

1. **有限代数の定義**
   - Boolean 演算で閉じた事象族
   - σ-代数の有限版

2. **基本的な性質**
   - 積・差で閉じている
   - 有限和・有限積で閉じている

3. **具体例**
   - 自明な代数：最小の代数
   - 全体の代数：最大の代数
   - 偶奇代数：サイコロの例

4. **可測関数**
   - 代数の構造を保存する写像
   - 恒等関数と合成

5. **構造塔との接続**
   - フィルトレーションの準備
   - minLayer による特徴づけの予告

### 次のステップへ

本ファイルにより、DecidableFiltration の実装準備が整った：

1. **DecidableFiltration.lean**（次のファイル）
   - StructureTowerWithMin のインスタンス化
   - 単調増加する代数の系列
   - minLayer = 初めて可観測になる時刻

2. **ComputableStoppingTime.lean**
   - 停止時間の定義
   - minLayer による特徴づけ
   - 具体的な停止時間の計算

3. **AlgorithmicMartingale.lean**
   - マルチンゲールの定義
   - Optional Stopping Theorem
   - 有限計算による証明

### 教育的価値

このファイルは以下を示している：

- **代数的構造の重要性**：事象の族も構造を持つ
- **段階的な情報の増加**：フィルトレーションの直感
- **構造塔との自然な対応**：layer = 代数

### 参考資料

- `DecidableEvents.lean`: 事象の基礎
- `CAT2_complete.lean`: 構造塔の完全な形式化
- Billingsley の *Probability and Measure*: 測度論の標準教科書

-/

/-!
## 演習問題（Exercises）

### 基礎問題

1. **代数の検証**
   - 与えられた事象族が代数をなすか判定せよ
   - 例：{∅, {1,2}, {3,4,5,6}, Ω} はサイコロ空間の代数か？

2. **生成される代数の計算**
   - 一つの事象 A から生成される代数を求めよ
   - 答：{∅, A, Aᶜ, Ω}

3. **可測関数の合成**
   - 可測関数の合成が可測であることを確認せよ

### 応用問題

4. **サイコロの分割代数**
   - サイコロを {1,2}, {3,4}, {5,6} に分割
   - この分割から生成される代数を構成せよ

5. **コイン投げのフィルトレーション**
   - 3回コイン投げの各時刻の代数を記述せよ
   - |ℱ₀| = 2, |ℱ₁| = 4, |ℱ₂| = 8, |ℱ₃| = 16 を確認

6. **可測関数の像**
   - なぜ可測関数の像は可測とは限らないか？
   - 反例を構成せよ

### 発展問題

7. **代数の交わりと和**
   - 二つの代数 ℱ, 𝒢 の交わり ℱ ∩ 𝒢 は代数か？
   - 和 ℱ ∪ 𝒢 はどうか？

8. **原子的事象**
   - 代数 ℱ の原子（atom）を定義せよ
   - 自明でない代数は常に原子を持つか？

9. **構造塔への応用**
   - 代数の単調増加列がどう StructureTower になるか
   - minLayer 関数の具体的な定義を考察せよ

10. **停止時間の構成**
    - 「初めて偶数が出る時刻」を停止時間として定義
    - これが代数のフィルトレーションでどう表現されるか
-/

# DecidableAlgebra.lean - 概要と使用ガイド

## 📚 概要

このファイルは、**有限代数**（finite algebra）を通じて事象の構造化された族を扱います。
σ-代数の離散版として、Boolean 演算で閉じた事象族を定義し、可測性の概念を導入します。

これは DecidableEvents.lean の自然な拡張であり、DecidableFiltration.lean（構造塔のインスタンス化）への重要な橋渡しとなります。

## 🎯 このファイルの位置づけ

```
DecidableEvents.lean      ← 事象の基礎（完成）
    ↓
DecidableAlgebra.lean     ← 今回（事象の族の構造）
    ↓
DecidableFiltration.lean  ← 次回（構造塔のインスタンス）
    ↓
ComputableStoppingTime    ← 停止時間
    ↓
AlgorithmicMartingale     ← マルチンゲール理論
```

## 🔑 主要な定義

### 1. FiniteAlgebra（有限代数）

```lean
structure FiniteAlgebra (Ω : Type*) where
  events : Set (Event Ω)
  has_empty : Event.empty ∈ events
  closed_complement : ∀ {A}, A ∈ events → Event.complement A ∈ events
  closed_union : ∀ {A B}, A ∈ events → B ∈ events → 
                 Event.union A B ∈ events
```

**意味**：Boolean 演算（補集合、和）で閉じた事象の族

**3つの公理**：
1. 空事象を含む（または同値に、全事象を含む）
2. 補集合で閉じている：A ∈ ℱ ⇒ Aᶜ ∈ ℱ
3. 和で閉じている：A, B ∈ ℱ ⇒ A ∪ B ∈ ℱ

### 2. 基本的な性質（派生定理）

#### 全事象の包含
```lean
theorem has_univ (ℱ : FiniteAlgebra Ω) : Event.univ ∈ ℱ.events
```
証明：∅ ∈ ℱ かつ補集合で閉じているので、∅ᶜ = Ω ∈ ℱ

#### 積で閉じている
```lean
theorem closed_intersection (ℱ : FiniteAlgebra Ω) 
    {A B} (hA : A ∈ ℱ.events) (hB : B ∈ ℱ.events) :
    Event.intersection A B ∈ ℱ.events
```
証明：A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ （De Morgan の法則）

#### 差で閉じている
```lean
theorem closed_diff (ℱ : FiniteAlgebra Ω)
    {A B} (hA : A ∈ ℱ.events) (hB : B ∈ ℱ.events) :
    Event.diff A B ∈ ℱ.events
```
証明：A \ B = A ∩ Bᶜ

### 3. 部分代数（SubAlgebra）

```lean
def IsSubalgebra (ℱ 𝒢 : FiniteAlgebra Ω) : Prop :=
  ℱ.events ⊆ 𝒢.events

notation:50 ℱ " ⊆ₐ " 𝒢:50 => IsSubalgebra ℱ 𝒢
```

**性質**：
- 反射的：ℱ ⊆ₐ ℱ
- 推移的：ℱ ⊆ₐ 𝒢 ∧ 𝒢 ⊆ₐ ℋ ⇒ ℱ ⊆ₐ ℋ

## 📊 具体例

### 例 1: 自明な代数（Trivial Algebra）

```lean
def trivial : FiniteAlgebra Ω where
  events := {Event.empty, Event.univ}
  ...
```

**含まれる事象**：
- ∅（空事象）
- Ω（全事象）

**意味**：
- 最小の代数
- 「何も観測できない」状態
- 確率論では時刻 0 の情報（初期状態）

### 例 2: 全体の代数（Power Set Algebra）

```lean
def powerSet : FiniteAlgebra Ω where
  events := Set.univ
  ...
```

**含まれる事象**：
- すべての事象（𝒫(Ω)）

**意味**：
- 最大の代数
- 「すべてを観測できる」状態
- 確率論では完全な情報

### 例 3: サイコロの偶奇代数

```lean
def evenOddAlgebra : FiniteAlgebra diceSample.carrier where
  events := {
    Event.empty,
    evenDice,
    Event.complement evenDice,
    Event.univ
  }
  ...
```

**含まれる事象**：
1. ∅（空）
2. {0, 2, 4}（偶数の目）
3. {1, 3, 5}（奇数の目）
4. {0, 1, 2, 3, 4, 5}（全体）

**意味**：
- 「偶数か奇数か」という情報のみが観測可能
- trivial より大きく、powerSet より小さい
- 部分的な情報の形式化

**包含関係**：
```
trivial ⊆ₐ evenOddAlgebra ⊆ₐ powerSet
  |          |                  |
  {∅,Ω}      {∅,偶,奇,Ω}        𝒫(Ω)
```

## 🔗 可測関数（Measurable Functions）

### 定義

```lean
structure MeasurableFunction {Ω Ω'}
    (ℱ : FiniteAlgebra Ω) (𝒢 : FiniteAlgebra Ω') where
  toFun : Ω → Ω'
  measurable : ∀ {B}, B ∈ 𝒢.events → (toFun ⁻¹' B) ∈ ℱ.events

notation:25 ℱ " →ₘ " 𝒢:24 => MeasurableFunction ℱ 𝒢
```

**意味**：
- 「観測可能な情報を保存する関数」
- Ω' で観測可能な事象 B の逆像 f⁻¹(B) が Ω で観測可能

### 基本的な可測関数

```lean
-- 恒等関数（常に可測）
def id (ℱ : FiniteAlgebra Ω) : ℱ →ₘ ℱ

-- 合成（可測性を保存）
def comp (g : 𝒢 →ₘ ℋ) (f : ℱ →ₘ 𝒢) : ℱ →ₘ ℋ
```

**重要な注意**：
- 可測関数の**逆像**は可測（定義）
- 可測関数の**像**は可測とは限らない（一般には成り立たない）

## 🌉 構造塔との接続

### フィルトレーションとは

**フィルトレーション**（filtration）= 単調増加する代数の系列

```
ℱ₀ ⊆ₐ ℱ₁ ⊆ₐ ℱ₂ ⊆ₐ ... ⊆ₐ ℱₙ
```

各 ℱₜ = 時刻 t で「可観測な事象の族」

### StructureTowerWithMin への対応

次のファイル（DecidableFiltration.lean）では：

```lean
structure DecidableFiltration where
  sampleSpace : FiniteSampleSpace
  timeHorizon : ℕ
  observableAt : ℕ → FiniteAlgebra sampleSpace.carrier
  monotone : ∀ s ≤ t, observableAt s ⊆ₐ observableAt t

instance : StructureTowerWithMin where
  carrier := FiniteAlgebra sampleSpace.carrier
  Index := ℕ
  layer := observableAt
  minLayer := fun ℱ => 
    -- ℱ が初めて observableAt に現れる時刻
    Nat.find (∃ t, ℱ = observableAt t)
  ...
```

### 対応表

| 構造塔の概念 | フィルトレーションの概念 | 確率論の意味 |
|------------|---------------------|------------|
| carrier    | 代数の全体          | 可観測事象族の空間 |
| Index      | 時刻 ℕ             | 離散時間 |
| layer n    | observableAt n     | 時刻 n の可観測代数 |
| minLayer   | 初出時刻           | 初めて観測可能になる時刻 |
| monotone   | 単調性             | 情報の単調増加 |

### 具体例：コイン投げのフィルトレーション

n 回コイン投げの標本空間 Ω = {H, T}ⁿ

```
時刻 0: ℱ₀ = {∅, Ω}                    -- 何も観測していない
        |ℱ₀| = 2

時刻 1: ℱ₁ = σ(1回目の結果)            -- 1回目まで観測
        |ℱ₁| = 4
        例：{∅, "1回目がH", "1回目がT", Ω}

時刻 2: ℱ₂ = σ(1,2回目の結果)          -- 2回目まで観測
        |ℱ₂| = 8

...

時刻 n: ℱₙ = 𝒫(Ω)                      -- すべて観測
        |ℱₙ| = 2ⁿ
```

**単調性の確認**：
```
ℱ₀ ⊆ₐ ℱ₁ ⊆ₐ ℱ₂ ⊆ₐ ... ⊆ₐ ℱₙ
```

各時刻で情報が増加（減少しない）

### 停止時間との対応

**停止時間** τ : Ω → ℕ は以下を満たす：
```
∀ t, {ω | τ(ω) ≤ t} ∈ ℱₜ
```

**構造塔の言葉では**：
- 事象 {τ ≤ t} の minLayer が ≤ t
- minLayer 関数による特徴づけそのもの

**例**：「初めて偶数が出る時刻」
```lean
def firstEven : diceSample.carrier → ℕ :=
  fun ω => if ω.val % 2 = 0 then 1 else 2

-- 停止時間の条件：
-- {firstEven ≤ t} ∈ observableAt t
```

## 📝 ファイルの構成

```
Part 0: DecidableEvents からの必要な定義
  - FiniteSampleSpace
  - Event の基本演算

Part 1: FiniteAlgebra の定義
  - 構造体の定義
  - 基本的な性質（has_univ, closed_intersection, closed_diff）
  - 部分代数の関係

Part 2: 具体的な例
  - trivial: 自明な代数
  - powerSet: 全体の代数
  - evenOddAlgebra: サイコロの偶奇代数

Part 3: 可測関数
  - MeasurableFunction の定義
  - 恒等関数と合成

Part 4: 構造塔との接続
  - フィルトレーションの説明
  - StructureTowerWithMin への対応
  - コイン投げの例

Part 5: Decidability
  - DecidableAlgebra 型クラス
  - trivial と powerSet の decidability
```

## ⚠️ 実装の注意点

### Sorry で残されている部分

1. **有限和・有限積の閉包**
   ```lean
   theorem closed_finite_union (ℱ : FiniteAlgebra Ω)
       {ι : Type*} [Fintype ι] {A : ι → Event Ω} 
       (hA : ∀ i, A i ∈ ℱ.events) :
       (⋃ i, A i) ∈ ℱ.events := by
     sorry  -- Finset.univ を使った帰納法
   ```

2. **偶奇代数の構成**
   ```lean
   def evenOddAlgebra : FiniteAlgebra diceSample.carrier where
     ...
     closed_complement := by sorry  -- 4ケースの分析
     closed_union := by sorry       -- 16ケースの分析
   ```

### 証明の方針

- **有限和の閉包**：Fintype の帰納法を使用
- **偶奇代数**：4つの事象それぞれについてケース分析

これらは原理的には機械的に証明可能（有限ケース）

### DecidableEvents との統合

現在は最小限の定義を再掲していますが、実際のプロジェクトでは：

```lean
import Prob.DecidableEvents
-- 再定義不要、import で使用
```

## 🚀 次のステップ

### 優先度 A：DecidableFiltration.lean（推奨）

**内容**：
- DecidableFiltration 構造体の定義
- StructureTowerWithMin のインスタンス実装
- 具体例：コイン投げ、サイコロのフィルトレーション

**重要性**：
- 構造塔理論との直接的な接続
- minLayer = 初めて可観測になる時刻
- 停止時間の準備

### 優先度 B：Sorry の埋め

**内容**：
- `closed_finite_union` の証明
- `closed_finite_intersection` の証明
- `evenOddAlgebra` の完全な構成

**学習価値**：
- Fintype の帰納法の練習
- ケース分析の実践

### 優先度 C：拡張例

**内容**：
- より複雑な代数の例
- 生成される代数の計算アルゴリズム
- 可測関数の具体例

## 📚 演習問題（難易度別）

### ⭐ 基礎問題

1. **代数の検証**
   - {∅, {1,2}, {3,4,5,6}, Ω} はサイコロ空間の代数か？
   
2. **生成される代数**
   - 一つの事象 A から生成される代数は？
   - 答：{∅, A, Aᶜ, Ω}

3. **包含関係**
   - trivial ⊆ₐ evenOddAlgebra ⊆ₐ powerSet を確認

### ⭐⭐ 応用問題

4. **サイコロの分割代数**
   - {1,2}, {3,4}, {5,6} の分割から生成される代数
   - 事象の個数は？

5. **コイン投げのフィルトレーション**
   - 3回コイン投げの ℱ₀, ℱ₁, ℱ₂, ℱ₃ を記述
   - |ℱₜ| = 2^(2^t) を確認

6. **可測関数の合成**
   - f : ℱ →ₘ 𝒢 と g : 𝒢 →ₘ ℋ の合成が可測

### ⭐⭐⭐ 発展問題

7. **代数の交わり**
   - ℱ ∩ 𝒢 は代数か？（Yes）
   - ℱ ∪ 𝒢 は代数か？（No、反例を構成）

8. **原子的事象**
   - 代数 ℱ の原子（atom）を定義
   - 自明でない代数は常に原子を持つか？

9. **停止時間の構成**
   - 「初めて偶数が出る時刻」を停止時間として実装
   - {τ ≤ t} ∈ ℱₜ を確認

10. **測度の拡張**
    - 代数上の確率測度を定義
    - Kolmogorov の拡張定理の離散版

## 📖 参考資料

### 本ファイルに関連

- `DecidableEvents.lean`: 事象の基礎（前提知識）
- `CAT2_complete.lean`: 構造塔の完全な形式化

### 次のステップ

- `DecidableFiltration.lean`: （次に作成）
- `ComputableStoppingTime.lean`: （将来）

### 数学の教科書

- **Billingsley**: *Probability and Measure* - σ-代数の標準的な扱い
- **Williams**: *Probability with Martingales* - フィルトレーションの直感的説明
- **Kallenberg**: *Foundations of Modern Probability* - より高度な理論

### Lean と形式化

- mathlib の MeasureTheory: 一般的な測度論
- mathlib の ProbabilityTheory: 確率論の形式化

## 🎓 教育的価値

このファイルが示すこと：

1. **段階的な抽象化**
   - 事象 → 事象族 → 構造化された事象族

2. **代数的構造の重要性**
   - Boolean 演算 = 代数的操作
   - 閉包 = 代数的完備性

3. **情報の形式化**
   - 代数 = 観測可能な情報
   - 部分代数 = 部分的な情報

4. **構造塔との自然な対応**
   - 単調増加 = 情報の蓄積
   - minLayer = 初出時刻

## ✅ まとめ

### 達成されたこと

✅ **有限代数の完全な定義**
- Boolean 演算で閉じた事象族
- σ-代数の離散版

✅ **基本的な性質の導出**
- 積・差で閉じている
- 派生定理の証明

✅ **具体例の構成**
- trivial, powerSet, evenOddAlgebra
- 包含関係の明示

✅ **可測関数の定義**
- 構造を保存する写像
- 恒等関数と合成

✅ **構造塔との接続の準備**
- フィルトレーションの概念
- 次のファイルへの明確な道筋

### 次の目標

🎯 **DecidableFiltration.lean**
- StructureTowerWithMin のインスタンス化
- 具体例の完全実装
- 停止時間への橋渡し

準備は完璧です！🚀

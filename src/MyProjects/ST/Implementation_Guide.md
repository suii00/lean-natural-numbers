# 確率論的構造塔 - 実装ガイド

## 現在の実装状況

### ✅ 完成している部分

1. **DiscreteFiltration** (`Claude_Probability.lean`)
   - 基本構造の定義
   - `toMeasurableTower`への変換
   - `trivial`と`product`の実装

2. **停止時刻の基本** (`Claude_Probability_Extended.lean`)
   - `StoppingTime`の定義
   - `const`, `min`, `max`の実装

### ⚠️ 未完成部分（sorry）の解決方法

## 1. minLayerStoppingTime の証明

### 問題箇所

```lean
def minLayerStoppingTime (F : DiscreteFiltration Ω) : StoppingTime F where
  τ := fun ω => (F.toMeasurableTower.minLayer ω : WithTop ℕ)
  adapted := by
    intro n
    -- sorry がある部分
```

### 解決アプローチ

**キーとなる洞察**: `{ω | minLayer ω ≤ n}`を分解する

```lean
{ω | minLayer ω ≤ n} = ⋃_{k=0}^n {ω | minLayer ω = k}
```

各`{ω | minLayer ω = k}`は、単点集合`{ω}`が層`k`で可測になる最小の時刻が`k`である点の集合です。

### 詳細な証明戦略

```lean
adapted := by
  intro n
  -- ステップ1: 集合の分解
  have decomp : {ω : Ω | (F.toMeasurableTower.minLayer ω : WithTop ℕ) ≤ n} =
      ⋃ k ∈ Finset.range (n + 1), {ω | F.toMeasurableTower.minLayer ω = k} := by
    ext ω
    simp [Finset.mem_range]
    constructor
    · intro h
      refine ⟨F.toMeasurableTower.minLayer ω, ?_, rfl⟩
      simp at h
      exact h
    · intro ⟨k, hk, heq⟩
      simp [heq]
      exact hk
  
  rw [decomp]
  
  -- ステップ2: 各 k について {ω | minLayer ω = k} の可測性
  apply MeasurableSet.biUnion
  · exact (Finset.range (n + 1)).countable_toSet
  
  intro k hk
  simp [Finset.mem_range] at hk
  
  -- ステップ3: minLayer ω = k の特徴づけ
  -- これは以下と同値：
  -- (a) {ω} は F.sigma k で可測
  -- (b) すべての j < k について、{ω} は F.sigma j で可測でない
  
  -- しかし (b) は「可測でない」という否定的条件なので扱いにくい
  -- 代わりに、単点集合の挙動を利用する別のアプローチが必要
```

### 別のアプローチ: 単調性を利用

実は、`point_measurable`の条件が弱い可能性があります。より強い条件を追加することを検討：

```lean
structure DiscreteFiltration (Ω : Type u) [MeasurableSpace Ω] where
  sigma : ℕ → MeasurableSpace Ω
  adapted : ∀ {m n : ℕ}, m ≤ n → sigma m ≤ sigma n
  bounded : ∀ n, sigma n ≤ (inferInstance : MeasurableSpace Ω)
  point_measurable : ∀ ω : Ω, ∃ n : ℕ, MeasurableSet[(sigma n)] ({ω} : Set Ω)
  
  -- 新しい条件: 各時刻で、その時刻までに可測になった点の集合が可測
  early_points_measurable : ∀ n : ℕ,
    MeasurableSet[(sigma n)] {ω | ∃ k ≤ n, MeasurableSet[(sigma k)] ({ω} : Set Ω)}
```

これにより、minLayerStoppingTimeの証明が容易になります。

## 2. naturalFiltration の point_measurable

### 問題

自然フィルトレーションでは、単点集合が可測になる保証がありません。

### 解決策

**Option 1**: 型`α`に追加の条件を要求

```lean
def naturalFiltration {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n))
    [MeasurableSingletonClass Ω] : -- Ω自体も単点可測
    DiscreteFiltration Ω where
  -- ... (前と同じ)
  point_measurable := by
    intro ω
    -- Ωが単点可測なので、{ω}は元のσ-代数で可測
    -- 従って任意の n で bounded により可測
    use 0
    have : {ω} = X 0 ⁻¹' {X 0 ω} := by
      ext x
      simp
      constructor
      · intro hx
        simp [hx]
      · intro hx
        have : x = ω := by
          -- これは一般には成り立たない！Xが単射である必要がある
        sorry
```

**Option 2**: より弱い構造を定義

```lean
/-- 単点可測性を要求しない、より一般的なフィルトレーション -/
structure GeneralFiltration (Ω : Type u) [MeasurableSpace Ω] where
  sigma : ℕ → MeasurableSpace Ω
  adapted : ∀ {m n : ℕ}, m ≤ n → sigma m ≤ sigma n
  bounded : ∀ n, sigma n ≤ (inferInstance : MeasurableSpace Ω)

/-- 自然フィルトレーションはGeneralFiltrationとして定義 -/
def naturalFiltrationGeneral {α : Type v} [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    GeneralFiltration Ω where
  -- ... (証明は簡単)
```

## 3. stoppedProcess の adapted 証明

### 問題

停止過程の可測性を示す必要があります。

### 解決アプローチ

```lean
adapted := by
  intro n
  -- X^τ_n(ω) = X_{min(n, τ(ω))}(ω)
  -- これは次の形：
  -- X^τ_n = Σ_{k=0}^n X_k · 𝟙_{τ=k} + X_n · 𝟙_{τ>n}
  
  -- ステップ1: 分解を書く
  have decomp : (stoppedProcessMin X τ).X n = 
      fun ω => if τ.τ ω ≤ n 
               then X.X (τ.τ ω).toNat ω 
               else X.X n ω := rfl
  
  -- ステップ2: 場合分けの可測性
  refine Measurable.ite ?_ ?_ ?_
  
  · -- {ω | τ ω ≤ n} が F.sigma n で可測（停止時刻の定義から）
    exact τ.adapted n
  
  · -- X_{τ(ω)} が {τ ≤ n} 上で F.sigma n 可測
    -- これは Σ_{k=0}^n X_k · 𝟙_{τ=k} の形
    sorry -- 詳細な証明が必要
  
  · -- X_n が {τ > n} 上で F.sigma n 可測（適合性から自明）
    exact X.adapted n
```

**詳細な証明**:

```lean
-- 第2項の証明
refine Measurable.subtype_mk ?_ _
apply Finset.measurable_sum
intro k hk
-- X_k · 𝟙_{τ=k}
apply Measurable.mul
· -- X_k は F.sigma k 可測、よって F.sigma n 可測（k ≤ n）
  have hmono := F.mono (Finset.mem_range.mp hk)
  exact Measurable.mono (X.adapted k) hmono le_rfl
· -- 𝟙_{τ=k} は F.sigma n 可測
  -- {τ = k} = {τ ≤ k} ∩ {τ ≤ k-1}ᶜ
  sorry
```

## 4. Martingale の martingale_property

### 簡単な例: 定数マルチンゲール

```lean
martingale_property := by
  intro m n hmn
  -- condexp (F.sigma m) (fun _ => c) =ᵐ (fun _ => c)
  have : condexp (F.sigma m) (fun _ : Ω => c) = fun _ => c := by
    exact condexp_const
  simp [this]
```

### 一般の stopped martingale

これはDoobの任意停止定理で、証明は複雑です。Mathlibに既存の補題があるかもしれません。

```lean
-- 有界停止時刻に対するDoobの定理
-- Mathlibの condexp と停止時刻の理論を組み合わせる
```

## 5. trivialMeasurableTower の minLayer_mem

### 問題

任意の型で単点集合が可測であるとは限りません。

### 解決策

```lean
def trivialMeasurableTower (α : Type v) [m : MeasurableSpace α] 
    [MeasurableSingletonClass α] :  -- この条件を追加
    MeasurableTowerWithMin where
  carrier := α
  Index := Unit
  indexPreorder := inferInstance
  layer := fun _ => m
  monotone := by intro _ _ _; rfl
  minLayer := fun _ => ()
  minLayer_mem := by
    intro x
    -- MeasurableSingletonClass により {x} は可測
    exact measurableSet_singleton x
  minLayer_minimal := by intro _ _ _; trivial
```

## 推奨される実装順序

1. **まず**: `trivialMeasurableTower`に`MeasurableSingletonClass`を追加
   
2. **次に**: `stoppedProcess`の適合性証明を完成
   - これは技術的だが標準的な証明
   
3. **その後**: `naturalFiltration`を`GeneralFiltration`として再定義
   - または追加の型クラス条件を追加
   
4. **最後に**: `minLayerStoppingTime`の証明
   - これが最も概念的に重要
   - `early_points_measurable`条件の追加を検討

## テスト戦略

各ステップで具体例を使ってテスト：

```lean
-- 自明なフィルトレーションでのテスト
example (Ω : Type*) [MeasurableSpace Ω] [MeasurableSingletonClass Ω] :
    let F := DiscreteFiltration.trivial Ω
    ∀ ω, (minLayerStoppingTime F).τ ω = 0 := by
  intro ω
  simp [minLayerStoppingTime, DiscreteFiltration.toMeasurableTower]
  -- minLayer は常に 0（すべての層が同じなので）
  sorry

-- 定数停止時刻との比較
example (Ω : Type*) [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (n : ℕ) :
    let F := DiscreteFiltration.trivial Ω
    (StoppingTime.const F n).τ = fun _ => n := rfl
```

## 次のステップの課題

証明が完成したら、次の発展課題に進めます：

1. **最適停止理論** (課題5)
   - Snell包絡線の定義
   - 最適停止時刻の一意性定理
   
2. **測度論への応用** (課題6)
   - Borel階層の構造塔表現
   - 複雑度の最小化定理

3. **高度なトピック**
   - 連続時間フィルトレーション
   - 予測可能停止時刻
   - Doobの分解定理

## 参考文献

- Kallenberg, "Foundations of Modern Probability"
- Durrett, "Probability: Theory and Examples"  
- Karatzas & Shreve, "Brownian Motion and Stochastic Calculus"
- Mathlib docs: `MeasureTheory.Function.ConditionalExpectation`

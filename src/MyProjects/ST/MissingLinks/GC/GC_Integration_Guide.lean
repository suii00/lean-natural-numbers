/-!
# Galois Connection to Structure Tower: Integration Guide

GC → ClosureOp → Rank → Tower の4層アーキテクチャ統合ガイド

## ファイル構成

```
GenCl.lean           -- Layer 4: GaloisConnection → ClosureOperator
GC_to_Rank.lean      -- Layer 3: ClosureOperator → Rank functions
GC_RankTower.lean    -- Layer 2: Rank → RankTower integration
GC_WithMin.lean      -- Layer 1: WithTop ℕ → ℕ (minLayer selection)
GC_Categorical.lean  -- Layer 0: Categorical glue
```

## Import 順序

推奨される import の順序：

```lean
import MyProject.GenCl            -- Layer 4
import MyProject.GC_to_Rank       -- Layer 3
import MyProject.GC_RankTower     -- Layer 2
import MyProject.GC_WithMin       -- Layer 1
import MyProject.GC_Categorical   -- Layer 0 (optional)
```

## 典型的なワークフロー

### Pattern A: GC から始める場合

1. **Layer 4**: GaloisConnection を定義
2. **Layer 3**: 閉包作用素から rankStab を構成
3. **Layer 2**: Ranked (WithTop ℕ) を構成
4. **Layer 1**: 条件が揃えば RankedFinite に昇格
5. **Output**: SimpleTowerWithMin を得る

### Pattern B: Closure から始める場合

1. **Layer 3**: ClosureOp を直接定義
2. **Layer 2-1**: 上記と同様

### Pattern C: Rank から始める場合

1. **Layer 2**: rank: X → WithTop ℕ を直接定義
2. **Layer 1**: finite_rank を証明して RankedFinite に

## 具体的な使用例

### Example 1: 線形包（Span）

```lean
-- Layer 4: GC の定義（省略可能、直接 Layer 3 へ）
-- Layer 3: span 演算を ClosureOp として定義

def spanClosure (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    GaloisRank.ClosureOp (Set V) := {
  cl := fun S => Submodule.carrier (Submodule.span K S)
  mono := sorry
  le_closure := sorry
  idempotent := sorry
}

-- Layer 2: 有限次元の場合、rankGen を定義
noncomputable def spanRank {K V : Type*} [Field K] [AddCommGroup V] 
    [Module K V] [FiniteDimensional K V] (v : V) : WithTop ℕ :=
  -- 最小の生成元数を計算
  sorry

-- Layer 1: 有限次元 ⇒ 全ての rank が有限
noncomputable def spanRankedFinite {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : 
    GCWithMin.RankedFinite V := {
  toRanked := { rank := spanRank }
  finite_rank := sorry  -- FiniteDimensional から
}

-- Output: 構造塔の取得
noncomputable def spanTower {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    GCWithMin.SimpleTowerWithMin V :=
  spanRankedFinite.toTowerWithMin
```

### Example 2: 位相的閉包

```lean
-- Layer 3: 位相的閉包を ClosureOp として
def topClosure (X : Type*) [TopologicalSpace X] :
    GaloisRank.ClosureOp (Set X) := {
  cl := closure
  mono := closure_mono
  le_closure := subset_closure
  idempotent := closure_closure
}

-- Layer 2: rankStab（安定化回数）
noncomputable def topRankStab {X : Type*} [TopologicalSpace X]
    (C : GaloisRank.ClosureOp (Set X)) (s : Set X) : WithTop ℕ :=
  C.rankStab s

-- Layer 1: コンパクト空間の場合、有限で安定
-- （追加の条件が必要、ここでは省略）
```

### Example 3: 自然数の閉包（計算可能版）

```lean
-- Layer 2: 直接 rank を定義（計算可能）
def natUpperRank (n : ℕ) (max : ℕ) : ℕ :=
  if n ≤ max then 0 else 1

-- Layer 1: RankedFinite の構成（計算可能）
def natUpperRankedFinite (max : ℕ) : GCWithMin.RankedFinite ℕ := {
  toRanked := { rank := fun n => (natUpperRank n max : WithTop ℕ) }
  finite_rank := fun n => ⟨1, by simp [natUpperRank]; omega⟩
}

-- 計算例
#eval natUpperRank 5 10  -- 0
#eval natUpperRank 15 10 -- 1
```

## 既存 RankTower との統合

### 統合ポイント

既存の `RankTower.lean` にある以下の構造と統合：

1. **StructureTowerWithMin**: GC_WithMin.SimpleTowerWithMin と対応
2. **towerFromRank**: GC_RankTower で実装済み
3. **rankFromTower**: Layer 2 で逆方向の構成

### 統合手順

```lean
-- 既存の import
import MyProjects.ST.RankCore.Basic
import MyProjects.ST.Rank.P3.RankTower

-- 新規ファイルの import
import MyProject.GC_WithMin

-- 型の同一視（必要に応じて）
def SimpleTowerWithMin_eq_StructureTowerWithMin :
    GCWithMin.SimpleTowerWithMin X ≃ 
    StructureTowerWithMin :=
  sorry  -- フィールドの対応を示す

-- GC 由来の塔を既存の型に変換
noncomputable def gcTowerToExisting 
    (T : GCWithMin.SimpleTowerWithMin X) :
    StructureTowerWithMin := {
  carrier := X
  Index := ℕ
  indexPreorder := inferInstance
  layer := T.layer
  covering := T.covering
  monotone := T.monotone
  minLayer := T.minLayer
  minLayer_mem := T.minLayer_mem
  minLayer_minimal := T.minLayer_minimal
}
```

## 設計原則の確認

### ✓ 制約の遵守

- [x] `def` / `structure` には `sorry` なし
- [x] `lemma` / `theorem` には `sorry` 使用可
- [x] rank の値域は Preorder（WithTop ℕ または ℕ）

### ✓ 優先順位

1. まず WithTop ℕ 版を作成
2. 条件が揃ったら ℕ に降ろす
3. 問題は Layer 1 に隔離

### ✓ 層のパターン

```lean
layer n := {x | rank x ≤ n}
```

により、以下が自明に：
- monotone: 順序の推移律から
- minLayer 特徴付け: rank の最小性から

## 被覆性の条件

各 rank 関数タイプで必要な条件：

| Rank タイプ | 被覆性の条件 | 例 |
|------------|-------------|-----|
| rankStab | Finite X または ACC | 有限集合、有限次元 |
| rankGen | 有限生成性 | 自由加群、有限生成イデアル |
| rankReach | 到達可能性 | グラフの距離 |

## トラブルシューティング

### Q1: "type mismatch" エラー

**原因**: WithTop ℕ と ℕ の混同

**解決**: 
```lean
-- NG
def rank : X → ℕ := ...
def layer n := {x | rank x ≤ (n : WithTop ℕ)}  -- 型不一致

-- OK
def rank : X → WithTop ℕ := fun x => (... : ℕ)
def layer n := {x | rank x ≤ n}
```

### Q2: "noncomputable" 警告

**原因**: Nat.find の使用

**解決**: `noncomputable` を付ける（Layer 1 の設計意図）

```lean
noncomputable def minLayer (x : X) : ℕ := ...
```

### Q3: 被覆性の証明が通らない

**原因**: 有限性条件の不足

**解決**: 
```lean
-- 条件を明示
theorem covering [Finite X] (C : ClosureOp X) :
    ∀ x, ∃ n, ... := ...
```

## 拡張方向

### 1. Ordinal への拡張

```lean
-- 現在: WithTop ℕ
def rank : X → WithTop ℕ := ...

-- 将来: Ordinal
def rank : X → Ordinal.{u} := ...
```

### 2. 連続版

```lean
-- 離散版
def layer (n : ℕ) : Set X := ...

-- 連続版
def layer (t : ℝ≥0) : Set X := ...
```

### 3. 確率論への応用

```lean
-- 停止時刻
def stoppingTime : Ω → WithTop ℕ := ...

-- マルチンゲール
def martingaleTower [IsFiniteMeasure μ] : 
    SimpleTowerWithMin (Ω → ℝ) := ...
```

## まとめ

このアーキテクチャにより：

1. **理論的明確性**: GC → Closure → Rank → Tower の段階的構成
2. **実装の柔軟性**: 各層で適切な抽象化レベル
3. **問題の隔離**: 停止時刻の有限性は Layer 1 のみ
4. **既存との整合**: RankTower.lean との統合が容易

使用時は：
- 単純な場合: Layer 2 から開始（直接 rank 定義）
- 理論的な場合: Layer 4 から開始（GC の性質を活用）
- 計算可能性重視: Layer 1 を避けて直接 def

-/

-- このファイルは説明用のため、実際のコードは含まない

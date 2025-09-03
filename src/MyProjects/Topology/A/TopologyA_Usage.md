# TopologyA: ext/simp の使い方と前提の要点

本ファイルの API を日常利用するための最小ガイドです。

- 代表的な補題・定義（主に `src/MyProjects/Topology/A/TopologyA.lean`）
  - 積の普遍性の同値: `continuous_iff_proj_continuous`
  - 指数法則（カリー化の同相）: `exponential_law : C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`
  - β-簡約（toEquiv/coe の両形式）:
    - `(exponential_law …).toEquiv F x y = F (x, y)`
    - `(exponential_law …) F x y = F (x, y)`
  - 評価のβ-簡約: `(fun p : C(Y, Z) × Y => p.1 p.2) (f, y) = f y`
  - 直積前合成の評価: `ContinuousMap.prodMap φ ψ (x, y) = (φ x, ψ y)`
  - 部分評価の連続性: `continuous_partial_right`, `continuous_partial_left`
  - 右変数側の前合成（点wise/bundled）:
    - `[simp] curry_comp_right_apply`
    - `curry_comp_right`

## ext; simp パターン（指数法則まわり）

- 典型: `ext x y; simp`
  - `simp` は `exponential_law` の β-簡約、`prodMap_apply`、`eval_apply` を用いて、
    ほぼ見た目通りに式を簡約します。

```lean
-- 例: 右変数側の前合成の整合性（点wise）
example {X Y Y' Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Y'] [TopologicalSpace Z]
    [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Y']
    (ψ : C(Y', Y)) (F : C(X × Y, Z)) (x : X) (y : Y') :
    ((exponential_law (X:=X) (Y:=Y') (Z:=Z)).toEquiv
      (F.comp (ContinuousMap.prodMap (ContinuousMap.id _) ψ)) x) y
    = ((exponential_law (X:=X) (Y:=Y) (Z:=Z)).toEquiv F x) (ψ y) := by
  simp
```

- 束ねた等式（bundled）の場合も `ext x y; simp` で終わります。

```lean
-- 例: 右変数側の前合成の整合性（bundled）
example {X Y Y' Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Y'] [TopologicalSpace Z]
    [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Y']
    (ψ : C(Y', Y)) (F : C(X × Y, Z)) :
    (exponential_law (X:=X) (Y:=Y') (Z:=Z)).toEquiv
        (F.comp (ContinuousMap.prodMap (ContinuousMap.id _) ψ))
    = (ContinuousMap.compRightContinuousMap (X:=Y') (Y:=Y) (Z:=Z) ψ).comp
        ((exponential_law (X:=X) (Y:=Y) (Z:=Z)).toEquiv F) := by
  ext x y; simp
```

## 前提（重要）

- 指数法則 `exponential_law`:
  - 必要: `[LocallyCompactSpace X] [LocallyCompactSpace Y]`
- 評価の連続性 `continuous_eval`:
  - 必要: `[LocallyCompactPair Y Z]`
- 実数の例（ℝ）
  - このリポジトリでは `import Mathlib.Topology.Instances.Real.Lemmas` を推奨。
  - 必要に応じて `import Mathlib.Topology.Algebra.Ring.Real` でも可。

## 補助：積の普遍性の同値の実務的使い方

- `Continuous h ↔ Continuous (π₁ ∘ h) ∧ Continuous (π₂ ∘ h)`
  - 分解: `have ⟨h₁, h₂⟩ := (continuous_iff_proj_continuous h).mp hh`
  - 合成: `(continuous_iff_proj_continuous h).mpr ⟨h₁, h₂⟩`

```lean
-- 例: 成分連続から積への連続を得る
example {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    {f : T → X} {g : T → Y}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun t => (f t, g t) := by
  simpa using hf.prodMk hg
```


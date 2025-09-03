# TopologyA — Bourbaki-style structuration of products and function spaces

本メモは `src/MyProjects/Topology/A/TopologyA.lean` の数学的内容を、ニコラ・ブルバキの「順序対と射（射影）による構造化」の精神に沿って要約・解説します。

- 主題
  - 積位相の普遍性（射影による特徴づけ）
  - 位相環（あるいは位相加群・群）における連続準同型の構造的補題
  - コンパクト開位相における指数法則（Currying）と評価写像の連続性
  - それらに付随する部分評価・前合成の整合性補題と、`ext; simp` による自動化


## 1. 積位相と普遍性：π₁, π₂ による特徴づけ

Lean 側では `MyProjects.Topology.BourbakiProductAndHom` 由来の射影
`π₁ : X × Y → X`, `π₂ : X × Y → Y` を用いて、積位相の普遍性を次で実装しています。

- `product_universal_property`（成分版）
  
  任意の型 `Z` と写像 `f : Z → X, g : Z → Y` について、
  
  `Continuous (fun z => (f z, g z)) ↔ Continuous f ∧ Continuous g`。
  
  これは「積への写像の連続性は成分の連続性に同値」という古典的事実です。

- `product_diagram_commutes`（図式版：射影との合成）
  
  `h : Z → X × Y` が連続なら、`π₁ ∘ h` と `π₂ ∘ h` はともに連続。

- `continuous_iff_proj_continuous`（普遍性の同値を h で直接述べる版）
  
  `Continuous h ↔ Continuous (π₁ ∘ h) ∧ Continuous (π₂ ∘ h)`。
  
  証明の骨子は、（→）は合成の連続性、（←）は `Continuous.prodMk` による成分からの組み立てです。

これらはいずれも「順序対（x,y）の第一・第二成分への射影が位相を生成し、積はそれらを最弱に保つ」という積位相の普遍性（ユニバーサルプロパティ）を明確化しています。


## 2. 位相環における連続準同型の構造補題

`[TopologicalSpace R] [Ring R] [IsTopologicalRing R]` と
`[TopologicalSpace S] [Ring S]` のもと、連続な環準同型 `f : R →+* S` が与えられると：

- `r ↦ f (r + r)` は連続
- `(p : R × R) ↦ f (p.1 * p.2)` は連続

いずれも、`r ↦ r + r` や `(p₁, p₂) ↦ p₁ * p₂` の連続性（位相環構造）と合成の連続性から従います。


## 3. 指数法則（カリー化）と評価の連続性（コンパクト開位相）

`C(X, Y)` を「連続写像の空間」とし、コンパクト開位相で位相空間とみなします。

- 指数法則（Homeomorph.curry）
  
  `exponential_law : C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`
  
  ただし仮定として `[LocallyCompactSpace X] [LocallyCompactSpace Y]` を要します。
  双方向の β-簡約（見たままの簡約）も `@[simp]` として提供されています：
  
  - `(exponential_law …).toEquiv F x y = F (x, y)`
  - `(exponential_law …) F x y = F (x, y)`（toEquiv の強制変換を省いた形）
  - 逆向きも同様に

- 評価写像の連続性（ContinuousEval）
  
  `[LocallyCompactPair Y Z]` のもと、評価
  `eval : C(Y, Z) × Y → Z, (f, y) ↦ f y` が連続。

- 部分評価の連続性
  
  `F : C(X × Y, Z)` に対し、任意の `y : Y` で固定すると
  `x ↦ F (x, y)` は連続（左変数固定でも同様）。

これらは関数空間の基本的操作（カリー化、評価、部分評価）が位相構造と整合することを示します。


## 4. 前合成（直積・カリー化）と整合性

- 第1変数側の前合成（bundled）：
  
  `φ : C(X', X)` と `F : C(X × Y, Z)` に対し、
  `(exponential_law (X:=X') …).toEquiv (F ∘ (φ × id)) = (exponential_law … F) ∘ φ`。

- 第2変数側の前合成（pointwise/bundled）：
  
  `ψ : C(Y', Y)` と `F : C(X × Y, Z)` に対し、カリー化と右側前合成の整合性を
  点wise版（`@[simp]`）と束ねた等式版の両方で用意しています。
  
  いずれも `ext x y; simp`（β-簡約と `prodMap` の簡約）で証明・利用できるように設計されています。


## 5. 自動化：`ext; simp` パターン

- `ext x y; simp` により、
  - `exponential_law` の β-簡約（curry/uncurry）
  - `ContinuousMap.prodMap` の評価
  - 評価写像の β-簡約
  が一気に解決され、指数法則まわりの等式は見た目通りに簡約されます。


## 6. 前提と実例

- 指数法則：`[LocallyCompactSpace X] [LocallyCompactSpace Y]`
- 評価連続性：`[LocallyCompactPair Y Z]`
- 実例（ℝ）
  - リポジトリ構成上、`import Mathlib.Topology.Instances.Real.Lemmas`（もしくは
    `import Mathlib.Topology.Algebra.Ring.Real`）を用いると、`ℝ` の必要な位相的性質が解決し、
    `ext; simp` の即時検証が可能になります。


## 7. ブルバキ的観点：順序対と射に基づく構造

- 順序対 `(x, y)` の第一・第二射影 `π₁, π₂` を基本的「構造射」とみなし、
  積位相はそれらを連続にする最弱の位相として特徴づけられます。
- カテゴリ的には、Top での積（普遍性）と、函手 `C(-, Z)` による指数法則（可換図式）は、
  射（写像）の作る図式の整合性として自然に現れます。
- 本ファイルは、これらの一般理論を Lean 上で直接扱える一連の補題群に落とし込み、
  `simp` 可能な β-簡約と `ext` による点ごとの同定を通じて、実務的な証明が
  構造の見た目通りに進むよう整備しています。


---

補足：使い方（戦略やコマンド）については `TopologyA_Usage.md` を参照してください。

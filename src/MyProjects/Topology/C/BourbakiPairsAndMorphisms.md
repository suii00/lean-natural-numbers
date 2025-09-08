# BourbakiPairsAndMorphisms — 順序対・射影・射のブルバキ的整理ノート

本ノートは `src/MyProjects/Topology/C/BourbakiPairsAndMorphisms.lean` の数学的背景と設計意図を、ニコラ・ブルバキ『数学原論』の精神（集合＝構造の担い手、順序対は射影で読む、構造射による圏的整理）に沿って解説します。

## 哲学（ブルバキ流）
- 構造は集合の上に与えられる。順序対 `(x, y)` は第一・第二射影 `π₁, π₂` で特徴づけられる（「順序対は射影で読む」）。
- 直積位相は「射影を連続にする最弱の位相」。したがって、積空間への写像の連続性は、射影合成の連続性で検査できる（普遍性）。
- 構造保存写像（群準同型など）は合成に関して閉じる。圏論的には対象（構造つき集合）と射（構造保存写像）からなる圏で表現される。
- 位相群では、群の基本射（積・逆・単位）が連続であることが「両立性」を表す。

## ファイル内の主な定義・定理と意味

### 1. 順序対と射影（Ordered pairs and projections）
- `π₁ : X × Y → X`, `π₂ : X × Y → Y`
  - 射影の明示名。証明用の補助として `continuous_π₁`, `continuous_π₂`（連続）。
- `@[continuity] continuous_pair_mk`
  - 連続 `f : X → Z`, `g : Y → W` から `p ↦ (f p.1, g p.2)` が連続。
  - 「成分が連続なら対の組も連続」＝直積の普遍性の具体化。

### 2. 普遍性の同値（射影での連続性検査）
- `continuous_iff_proj_core / continuous_iff_proj`
  - 同値: `Continuous h ↔ (Continuous (π₁ ∘ h) ∧ Continuous (π₂ ∘ h))`。
  - 証明スケッチ: `→` は射影の連続性と合成の連続性から直ちに従う。`←` は `Continuous.prodMk`（成分連続からペア連続）で従う。
- 片向きの構成子（simp ループ回避のため属性なし）
  - `continuous_of_proj (h₁) (h₂) : Continuous h`。
  - 射影を取り出す側は `continuous_proj_fst/snd` を用意（`Continuous h` から各成分の連続性）。

### 3. 右三角恒等式（成分版）と正規化
- 点ごとの rfl による安定的な正規化（`simp` で即約）
  - `@[simp] fst_comp_pair (f g) : (fun t => (f t, g t).1) = f`
  - `@[simp] snd_comp_pair (f g) : (fun t => (f t, g t).2) = g`
- `Prod.map` と射影の橋渡し（関数合成位置でも収束）
  - `@[simp] fst_comp_Prod_map (f g) : Prod.fst ∘ Prod.map f g = f ∘ Prod.fst`
  - `@[simp] snd_comp_Prod_map (f g) : Prod.snd ∘ Prod.map f g = g ∘ Prod.snd`
- 合成の押し込み・恒等除去（既存の補助と整合）
  - `@[simp] prod_map_comp`：`Prod.map` の合成は成分合成へ正規化。
  - `@[simp] prod_map_id_id`：恒等成分の `Prod.map` は恒等。

### 4. `Prod.map` の連続性ラッパ
- `@[continuity] continuous_Prod_map (hf hg)`
  - `h := Prod.map f g` に対して `continuous_iff_proj_core` の `→` を用いて、
    `simp [Prod.map]` で両成分の連続性に帰着。`by continuity` と相性良好。
  - エラー “expected `Continuous (Prod.map f g)` but got `∧`” を避けるための一本釣り補題。

### 5. 群準同型とその合成
- `groupHomComp (φ : G →* H) (ψ : H →* K) : G →* K` とその正規化
  - `@[simp] groupHomComp_apply`, `@[simp] groupHomComp_eq_comp`。
  - 単位律（型パラメータを明示して推論の迷いを回避）
    - `@[simp] groupHomComp_id_left`, `@[simp] groupHomComp_id_left'`, `@[simp] groupHomComp_id_right`。
- 連続性ブリッジ
  - `@[continuity] continuous_groupHomComp φ ψ hf hg : Continuous (fun g => ψ (φ g))`。

### 6. 位相群における逆写像の合成
- 事前合成（定義域の反転）: `@[continuity] topological_group_hom_continuous_precomp_inv`
  - 仮定 `[IsTopologicalGroup G]` のみを要求。
- 事後合成（終域の反転）: `@[continuity] topological_group_hom_continuous_postcomp_inv`
  - 仮定 `[IsTopologicalGroup H]` のみを要求。
- いずれも `continuous_inv` と合成の連続性から即座に従う。

## 使い方のスケッチ（Lean）

```lean
-- 成分連続 ⇒ ペア/Prod.map 連続
have hf : Continuous f := …
have hg : Continuous g := …
exact MyProjects.Topology.C.continuous_pair_mk hf hg
exact MyProjects.Topology.C.continuous_Prod_map hf hg
-- あるいは
by continuity  -- 属性登録済により自動で解決

-- 普遍性（同値）
have h₁ : Continuous fun t => (h t).1 := …
have h₂ : Continuous fun t => (h t).2 := …
exact (MyProjects.Topology.C.continuous_iff_proj (h:=h)).2 ⟨h₁, h₂⟩
-- 片向きの構成子版
exact MyProjects.Topology.C.continuous_of_proj (h:=h) h₁ h₂

-- 正規化：`Prod.map` と射影
simp [Function.comp]  -- `fst_comp_Prod_map`, `snd_comp_Prod_map` が作動

-- 群準同型の合成（`simp` で点ごとに正規化）
by have := MyProjects.Topology.C.groupHomComp_apply φ ψ g; simpa using this

-- 位相群の反転合成
have hf : Continuous f := …
exact MyProjects.Topology.C.topological_group_hom_continuous_postcomp_inv f hf
```

## 設計上の注意
- `continuous_iff_proj` は強力ですが、`simp` への登録は避け、
  代わりに片向きの `continuous_of_proj` を提供して簡潔な構成を実現。
- “右三角恒等式（成分版）”は点ごと `rfl` で、`ext p; cases p; simp` 文化と互換。
- `Prod.map` まわりは「合成は内側へ押し込む」正規形（`prod_map_comp`）と
  射影ブリッジ（`fst/snd_comp_Prod_map`）で収束を安定化。
- 位相群の補題は必要最小のインスタンス範囲に分離（未使用警告を回避）。

## 参考となる普遍性の読み替え
- 直積の普遍性（`Top` の積対象）: 任意の `h : T → X × Y` が連続であることは、
  `π₁ ∘ h` と `π₂ ∘ h` の両方が連続であることに同値。
- 本ファイルの `continuous_iff_proj` はこの事実を Lean 用 API として固定化したもの。
  その一方向版 `continuous_of_proj` は、“構成的に対を作る”場面で特に有用です。

以上により、順序対・射影・射の関係を、ブルバキ的視点（構造＋射）で Lean 上に明示化し、
`simp` と `by continuity` で安定的に収束する正規形を整えています。


# D セクション実装メモ（今回の追加）

本ノートは、`D` ディレクトリで今回実装した内容の要点を、スナップショットに優しい（apply-only, pointwise `@[simp]`, no loops）方針で整理したものです。カテゴリ側（TopCat, Monad）と、関数空間側（compact–open）を分離し、相互に疎結合で使えるようにしています。

## 1. 対角–直積随伴とモナド（TopCat 側）

- 対角–直積の随伴（Δ ⊣ ×）を TopCat 上に構成。
  - 二変数積関手 `prodFunctorTop` と、Hom 集合同値 `diagProd_homEquiv` を用意。
  - `diagProdAdjunction : Functor.diag ⊣ prodFunctorTop` を `mkOfHomEquiv` で構成。
- 随伴からのモナド `productMonad` を導入（`Adjunction.toMonad`）。
- `η/μ` の「成分版」@[simp, reassoc] を固定（射影に落とす、点ごと `rfl`）：
  - `productMonad_eta_comp_fst/snd`（左三角の成分版）
  - `productMonad_mu_comp_fst/snd`（flatten：`((X×X)×(X×X)) ⟶ (X×X)` の射影合成）
- モナド法則の「成分版」@[simp, reassoc]（Option B）：
  - 右単位の成分版 `productMonad_right_unit_comp_fst/snd`
  - 結合の成分版 `productMonad_assoc_comp_fst/snd`
  - 証明はいずれも `productMonad.right_unit/assoc` に射影後 `simp [Category.assoc, comp_id]`。

関連ファイル:
- `src/MyProjects/Topology/D/ClaudeD.lean`
  - モナド生成と η/μ の成分版、モナド法則の成分版を実装

## 2. Kleisli（最小）

- Kleisli の「定義展開」は Mathlib 側の等式（`rfl`）をそのまま利用。
- 本リポジトリでは、Kleisli 側は**点ごと**の簡約（`ext; simp [Category.assoc]`）が通るよう、TopCat と混ぜないポリシーを維持。
- そのため、本体は D に集約し、Kleisli の薄い補助は必要最小限にとどめています。

## 3. 関数空間（compact–open）側との橋渡し（参考）

- `B` セクションに、compact–open 上の指数法則（`Homeomorph.curry`）を pointwise `@[simp]` で整備：
  - `src/MyProjects/Topology/B/ExpLawCO.lean`
    - `expLawCOHomeo` と β/η、X/Y 側前合成・Z 側後合成の自然性 `_apply` 補題
  - `src/MyProjects/Topology/B/ExpLawCO_Nat.lean`
    - `NatHomeoInX / NatHomeoInY`（TopCat を使わないナチュラル同型風の薄い梱包）
- これらは D とは独立に利用可能で、`ext; simp` により curry/uncurry を**点ごと**で正規化できます。

## 4. 使い方のヒント

- Kleisli 合成の正規形：
  1) Kleisli 合成を定義展開（`… ≫ productMonad.map … ≫ productMonad.μ.app _`）
  2) `ext; simp [Category.assoc]`
     - η/μ の成分版 + 右単位/結合の成分版が効き、**flatten の射影**まで一撃で落ちます。

- compact–open 側（`ExpLawCO`）では、curry/uncurry は `_apply` に `@[simp]` を付けた**点ごと**正規化のみを提供。外側の TopCat とは混ぜず、必要に応じて D 側とは別レイヤーとして併用してください。

## 5. スタイルと方針

- apply-only／pointwise `@[simp]`／no loops。
- `simp` は `_apply` や射影成分のみに登録（外向きの大きな書き換えは避ける）。
- TopCat 側（随伴・モナド）と compact–open 側（連続写像の空間）は**疎結合**。

## 6. 今後の小さい拡張候補

- Kleisli の便利補題（pointwise 版）を少量追加（`simp [Category.assoc]` で収束する形）。
- compact–open の自然性を `NatIso` 風に Y 側についても軽量梱包（既に `NatHomeoInY` を追加済み）。
- ループ・懸垂のスキャフォールドを ContinuousMap 限定で用意（点ごと三角恒等式の骨格）。

---

ビルド状態: `lake build MyProjects.Topology.D.ClaudeD` はグリーンです。疑問点や次の拡張の希望があればお知らせください。
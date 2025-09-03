# TopologyA: 企図と現状まとめ

本メモは、Bourbaki 的「順序対（台集合, 構造）と射（射影）化」の精神に基づく実装方針（企図）と、現在の `TopologyA.lean` の内容（現状）を対比して整理したものです。

対象ファイル: `src/MyProjects/Topology/A/TopologyA.lean`

## 企図（当初の実装方針）

- 構造化空間 TopPair
  - 台集合 `E` と位相 `τ` の順序対として表現。
  - 射は「構造保存写像」= 連続写像 `Hom`（連続性を備えた関数の束）。
  - 直積 `X ⨯ Y` を積位相で与え、射影 `proj₁, proj₂` と対写像 `pair` を用意。
  - 積の普遍性（存在・一意）および関数形 `Continuous (fun z => (f z, g z)) ↔ Continuous f ∧ Continuous g`。

- 連続写像空間 C(X,Y) と評価・指数法則の基礎
  - `C(X,Y)` に、全関数空間 `(X → Y)` の積位相からの誘導位相を付与。
  - 評価写像 `eval : C(X,Y) × X → Y` の連続性。
  - `curry : C(X×Y, Z) → C(X, C(Y, Z))` と `uncurry : C(X, C(Y, Z)) → C(X×Y, Z)` の連続性。
  -（将来拡張）`Y` 局所コンパクトなどの条件下で、コンパクト開位相により指数法則を `Homeomorph` まで。

- 位相群・位相環と連続準同型の束
  - 位相群（環）の順序対（台集合・位相・代数構造・位相的整合性）。
  - 連続準同型を束ねた型 `Hom` を定義（`MonoidHom`/`RingHom` + 連続性）。
  - 合成・恒等・積・射影・対写像・（将来）商や誘導/余誘導に対する一撃の連続性補題。

- Bourbaki τ レイヤ（集合族としての位相）
  - 開集合族 `Tau E` を構造体として定義（`∅, univ, 任意合併, 有限交叉` で閉）。
  - `Tau ↔ TopologicalSpace` の往復関数。
  - 族レベルの基本操作：生成 `generateFrom`、誘導 `induced`、余誘導 `coinduced`、直積 `prod`。

## 現状（`TopologyA.lean` に含まれるもの）

- TopPair と連続射
  - `structure TopPair`（台 `E` と位相）
  - `def Hom (X Y) := { f : X.E → Y.E // Continuous f }` と `Coe` を実装
  - `Hom.id`・`Hom.comp`・`@[simp] comp_apply`

 - 直積と普遍性
  - `def prod (X Y)`：積位相の TopPair、記法 `X ⨯ Y`
  - `def proj₁`, `def proj₂` と `def pair (f g)` を実装
  - 普遍性補題を復元・証明済み：
    - `@[simp] proj₁_pair`, `@[simp] proj₂_pair`
    - 一意性 `pair_unique`
    - η-則 `pair_eta`

- C(X,Y) と評価・カリー化（実装あり）
  - `abbrev C X Y := Hom X Y`
  - 誘導位相 `instance instTopC : TopologicalSpace (C X Y)`
  - `def eval : C(X,Y) × X → Y` とその連続性（名称の衝突回避のためローカル名で証明）
  - `def curry`, `def uncurry`：連続性の証明付き

- 位相群/位相環（部分実装の痕跡）
  - `TopGrp`/`TopRing` 名前空間の定義・草案が残存
  - 古い API（`TopologicalGroup`/`TopologicalRing`）や型クラス前提の不足、`prod_mk` の非推奨などにより、ビルド不整合がある状態

- Bourbaki τ レイヤ（実装あり）
  - `structure Tau (E)` と公理
  - `Tau.toTopologicalSpace` / `Tau.ofTopologicalSpace`
  - 基本操作：`induced`, `coinduced`, `prod`, `generateFrom`
  -（一部、記号化けや識別子の崩れが見受けられるため要整備）

## 既知の課題（現状のソースに起因）

- 文字コード起因の記号化け
  - `↦, ↔, ×, ⨯` などの Unicode 記号やギリシャ文字が壊れ、`ↁE, ÁE, ρE` といった不正トークン化が発生。
  - `import はファイル先頭` エラーは、先頭の不可視文字（BOM/ゼロ幅空白）や壊れたコメント起因の可能性。

- API の差分・非推奨
  - `Continuous.prod_mk` → `Continuous.prodMk` への変更が必要。
  - `TopologicalGroup`/`TopologicalRing` は `IsTopologicalGroup`/`IsTopologicalRing` に置換が必要。

- 識別子の不整合・未完成部
  - `proj₁E`/`proj₂` の命名が混在、関連補題の途中状態が残存。
  - 一部の補題・定義がコメントアウトのまま、あるいは未証明。

## 推奨する修正方針（非破壊・段階的）

- 文字コードの安定化
  - `TopologyA.lean` を UTF-8（BOM なし）で保存し、先頭に不可視文字がないことを確認。
  - Unicode 記号は Lean が受け付けるもののみを使用（必要に応じて ASCII へ置換）。

- TopPair 層の安定化（優先）
  - `pair/proj₁/proj₂` と普遍性補題をまず整合・完了。
  - `prod_mk` → `prodMk`、名前の統一（`proj₁`/`proj₂`）。

- C(X,Y) 層の完成度向上
  - `continuous_eval` の名前衝突回避（ローカル名使用）確認。
  - `Cpair Y Z` の導入により `C(X, C(Y,Z))` を安定に扱う設計の維持。

- 位相群/環の再導入（別ファイルで追加）
  - `IsTopologicalGroup`/`IsTopologicalRing` を用いた `Pair` と `Hom` を `TopologyA/Group.lean`, `TopologyA/Ring.lean` として追加（既存ファイルは非変更）。
  - 合成・積・射影・対写像・商（必要なら）に対する連続性ラッパー補題を充実。

- τ レイヤの整備
  - 記号化けの解消と識別子の統一。
  - 族 API（生成・誘導・余誘導・直積）を小さくテストしつつ拡張。

## 参考：今後の拡張マイルストーン

- 指数法則の Homeomorph（条件付き）
  - `C(X×Y, Z) ≃ₜ C(X, C(Y, Z))` を、`Y` 局所コンパクト＋コンパクト開位相の設定で提供。

- 商や関手的構成の「一撃補題」
  - 連続写像の像・逆像、商（群/環）・（余）誘導に対して、図式可換性から連続性を直接使える API を整備。

---

ご要望に応じて、上記の「非破壊・段階的」方針でパッチを小分けに追加します。まずは TopPair 層の普遍性補題の完成と、文字コード起因エラーの解消から着手するのが安全です。

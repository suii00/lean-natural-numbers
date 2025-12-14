# エラー修正ログ（`P5/P5_Applications.lean`）

対象ターゲット: `MyProjects.ST.CAT.Cat_D.P5.P5_Applications`

### エラー修正ログ
- エラー概要：
  - `ℕ∞` が未定義でパースが崩れ、以降の宣言が連鎖的にエラーになっていた（`expected token` / `unexpected token`）。
  - `SimpleGraph.Reachable` が未importで到達可能性を使う部分が壊れていた。
  - `reachabilityTower` が `Index := ℕ` のまま「到達不能を ⊤ に送る」設計になっており、被覆性（`covering`）を満たせず `sorry` が残っていた。
  - `ℚ` が未importで暗黙変数（しかも `Prop`）として導入され、`deriving DecidableEq` が非計算的になってコンパイルに失敗していた。
  - `def ... : TowerD` の `.Index` が型クラス推論で十分に展開されず、`layer 0` 等の数値リテラルが `OfNat ...` で失敗していた。
  - `simp` でゴールが閉じた後に `decide` が続き、`No goals to be solved` が発生していた。

- 原因：
  - `ℕ∞`（`ENat`）と `Reachable` は別ファイル定義であり、`import` 不足でトークン/定義が環境に無かった。
  - 「到達不能→∞」をやりたいのに `Index := ℕ` のままだと、∞ を入れる層が存在せず、一般のグラフで `covering` が立たない。
  - `ℚ` 記法が無い状態で `ℚ → ...` と書くと、Lean の `autoImplicit` により未宣言識別子 `ℚ` が暗黙変数として補われ、意図した有理数型にならない。
  - `TowerD` の返り値から `.Index` を取り出すとき、型クラス推論が `def` を十分に unfold せず、`OfNat (someTower n).Index 0` を `OfNat ℕ 0` に還元できないことがある。
  - `simp` がその場でゴールを閉じるケースがあり、後続 tactic が不要になっていた。

- 修正内容：
  - `P5/P5_Applications.lean` で以下を追加 import：
    - `Mathlib.Data.ENat.Basic`（`ℕ∞`）
    - `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`（`SimpleGraph.Reachable` と `Walk`）
    - `Mathlib.Data.Rat.Init`（`ℚ` 記法）
  - `distance` を `Reachable` から「歩道（walk）の長さが存在する」ことを経由して `Nat.find` で `ℕ∞` を返す形に修正。
  - `reachabilityTower` の `Index` を `ℕ∞` に変更し、`covering` を `⟨distance G s v, le_rfl⟩` で証明（`sorry` を撤去）。
  - `lineGraph5` / `completeGraph` の `loopless` を正しい型で証明し直し（`omega` 依存も削除）。
  - `cantorBendixsonTower` / `algebraicNumberTower` / `homologicalDimensionTower` に `@[reducible]` を付与して `OfNat` 失敗を解消。
  - `simp` の後に残っていた不要な `decide` を削除して `No goals to be solved` を解消。
  - docstring（`/-- ... -/`）が「宣言以外（`variable` など）」や「docstring→docstring」にぶつかっていた箇所を、通常コメント（`/- ... -/`）に変更。

- 修正が正しい理由：
  - Cat_D の公理（特に `covering`）を、追加仮定（連結性など）なしで満たすためには「∞ を入れられる Index」が必要で、`Index := ℕ∞` は意図に最も忠実。
  - `distance` は「到達可能なら有限長の walk がある」という事実だけを使って最小値を `Nat.find` で選ぶため、数学的意味（最短距離）と整合する。
  - `@[reducible]` は数学的内容（`Index := ℕ` など）を変えず、型クラス推論に必要な unfold だけを許す最小修正。
  - `No goals to be solved` は tactic の余分さが原因なので、不要行を削るのが根治。

- 動作確認：
  - 2025-12-14: プロジェクトルートで `lake build MyProjects.ST.CAT.Cat_D.P5.P5_Applications` が成功。

- どういう意図でこの実装に至ったかメモ
  - 「到達不能→∞」という仕様が既にコメントで示されていたため、`Index := ℕ` のまま無理に `covering` を作るのではなく、仕様に合わせて `Index` 側を拡張する方がブルバキ的（構造を先に整える）で安全だと判断した。
  - `ℚ` / `ℕ∞` / `Reachable` は “名前が使える” だけでは不十分で、トークン/記法や定義を提供する import が必要なので、まずそこを最短で補った。
  - Example の `OfNat` 問題は、注釈をばら撒くより `@[reducible]` の方が可逆で、記述も簡潔になるため採用した。

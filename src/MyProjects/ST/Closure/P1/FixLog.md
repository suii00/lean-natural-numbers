# エラー修正ログ（P1/Basic.lean）

## エラー概要
- `Mathlib.Data.Rat.Basic` / `Mathlib.Order.ClosureOperator` が見つからずビルド失敗。
- `minBasisCount` の定義が決定不能扱いとなり、`noncomputable` 指定が漏れていた。
- `layer` の定義依存で `OfNat linearSpanTower.Index n` を合成できず、例題が型エラー。
- `minBasisCount` 系の補題に `sorry` が残り証明未完了。
- スカラー倍保存補題で零・非零のケース分けが不足しゴール未解決。
- 統合版 `LinearSpanTower_Integrated.lean` で 0 層の例における `OfNat` 不足・型不一致（216, 223 付近）と、例題の型注釈不足によりビルドが止まった。

## 原因
- mathlib の実際のパスが `Mathlib.Data.Rat.Lemmas` / `Mathlib.Order.Closure` であり、存在しないファイルを import していた。
- `minBasisCount` を if のネストで書いたが、全体が classical 判定に依存しコンパイラが実行コードを生成できなかった。
- `layer n` をパターンマッチで定義していたため、例題中で `Index` の数値リテラルに必要な `OfNat` インスタンスを Lean が合成できなかった。
- 補題証明の多くを `sorry` で仮置きしており、ビルド時に未解決ゴールが残った。
- スカラー倍の補題は零ベクトル・軸上・一般位置の3ケースで非零性を示す補題が不足していた。
- 統合版では 0 層を集合同値で示す際に ext でなく membership ベースに分解しておらず、`OfNat` も明示しなかったためリテラル推論が失敗し、`minBasisCount = 0` から座標ゼロへの導出が詰まっていた。

## 修正内容
- import を存在するモジュール (`Mathlib.Data.Rat.Lemmas`, `Mathlib.Order.Closure`) に差し替え。
- `minBasisCount` を座標の零判定に基づく非計算的関数として再定義し、`noncomputable` を付与。
- `layer n := {v | minBasisCount v ≤ n}` とし、`minLayer` も同関数を返すことで `OfNat` 問題を解消。
- 零・軸上・一般位置の補題をすべて証明済みにし、`minBasisCount_general/axis_left/axis_right` を追加。
- スカラー倍保存補題を座標ごとの場合分けで書き直し、必要な非零性 (`mul_ne_zero`) を明示して解決。
- 例題での数値に `(0 : ℕ)` など明示的な型注釈を付け、`simp` の不要引数を削減。
- 統合版では 0 層の例を「零ベクトルが入る」「0 層なら零ベクトルに限る」の2補題に分解し、`(0 : ℕ)` を明示、`minBasisCount v = 0` から座標ゼロを導出するロジックを整理してビルドを通した。

## 修正が正しい理由
- mathlib の実在モジュールのみを import しているため解決不能エラーが消失。
- `minBasisCount` を零・軸上・一般位置で 0/1/2 と決定する仕様を補題群でカバーし、`layer` を単調性・被覆性を満たす形に落とし込んだため構造塔の公理を満たす。
- スカラー倍が零・非零を保存することを各ケースで示し、`minBasisCount` の値が変わらないことを論理的に証明している。
- すべての `sorry` を除去し、Lean の型検査を通過したことをもって正当性を確認。
- 統合版 0 層補題を membership 形式に再構成し、`minBasisCount v = 0` から `v = (0,0)` を直接導いたため、`OfNat` や ext の不足で詰まる箇所が解消されている。

## 動作確認
- プロジェクトルートで `lake build MyProjects.ST.Closure.P1.Basic` を実行しビルド成功（2025-12-02）。
- プロジェクトルートで `lake build MyProjects.ST.Closure.P1.LinearSpanTower_Integrated` を実行しビルド成功（警告のみ、2025-12-02）。

## どういう意図でこの実装に至ったかメモ
- Bourbaki 的「閉包作用素」観点を保ちつつ、`layer` を minBasisCount のしきい値で定義することで閉包の単調性・被覆性・最小層判定を同一関数で統一。
- 例題は教育目的のまま残しつつ、型エラーを避けるために数値リテラルへ明示的な型を付与。
- 最小限の差分でビルドを通し、今後の拡張（他の閉包作用素例）に備えて補題の粒度を揃えた。
- 統合版でも同じ思想を貫き、CAT2 完全定義との整合性を保ちながら最小限の変更で 0 層・1 層の例を通し、将来の高次元・他体拡張時に再利用しやすい形にした。

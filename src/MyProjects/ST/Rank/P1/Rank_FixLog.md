# エラー修正ログ（MyProjects.ST.Rank.P1.Basic）

## エラー概要
- `OfNat (finsetSizeTower ℕ).Index n` が合成できず、例題で数値リテラルが型不一致。
- 空集合・単集合リテラルで `EmptyCollection` / `Singleton` インスタンスが見つからず失敗。
- `primeFactorCount` を `factorization` 由来で定義しようとして `Nat.factors` 相当が環境に無く、定義・例ともに評価できず `native_decide` が失敗。
- 誤って `Mathlib.Data.Nat.Prime` / `Mathlib.Data.Nat.Factorization` を import し、存在しないパスでビルドエラー。
- ディレクトリの混乱（Closure と Rank を取り違えた）で最初に別ディレクトリを操作していた。

## 原因
- 例題の添字を `ℕ` と明示していなかったため `OfNat` が合成されなかった。
- `Finset` リテラルで型注釈を付けず、`EmptyCollection` / `Singleton` の型推論が止まった。
- 使用中の mathlib には `Nat.factorization` でなく `Nat.primeFactorsList` が提供されており、定義が環境非対応だった。
- import パスを mathlib に存在しないモジュール名で書いていた。
- 最初に `ST/Closure` 側を見てしまい、対象ディレクトリを誤解していた。

## 修正内容
- 例題の添字をすべて `(0 : ℕ)`, `(1 : ℕ)`, `(2 : ℕ)` に注釈し、`Finset` リテラルにも `: Finset ℕ` を明示。
- `primeFactorCount` を `Nat.primeFactorsList n.val` の長さで定義し直し、例も `native_decide` で検証できるように変更。
- import を `Mathlib.Data.Nat.Prime.Basic` と `Mathlib.Data.Nat.Factors` に修正、`Mathlib.Tactic` を追加。
- ビルド対象を正しく `MyProjects.ST.Rank.P1.Basic` で確認。

## 修正が正しい理由
- `Index = ℕ` でのリテラルに型注釈を付けたことで `OfNat` 合成が確実になり、例題が型エラーを起こさない。
- `primeFactorCount` を現行 mathlib の `primeFactorsList` に基づけたため、定義も計算例も評価可能になり `native_decide` が通る。
- 存在するモジュールだけを import しているためビルド時のファイル探索エラーが消失。

## 動作確認
- プロジェクトルートで `lake build MyProjects.ST.Rank.P1.Basic` を実行しビルド成功（2025-12-04）。

## どういう意図でこの実装に至ったかメモ
- Rank 型構造塔の一般パターンを示すファイルであり、例題・補題を最小修正で通して、他分野へのテンプレートとして再利用できるようにした。
- 数値注釈と既存 API への合わせ込みで、環境差異に強い形に整えた。

## ディレクトリ混乱に関する考察
- 当初 `ST/Closure` 側で作業し誤認していたが、実際の依頼は `ST/Rank/P1` 下の `Basic.lean` / `Claude.md` だった。今後は `Add context` で示されたパスを再確認し、`lake build <ターゲット>` も対象パスで実行するよう注意する。

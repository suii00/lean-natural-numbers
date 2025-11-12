# StructureTower_TestSuite 現状報告

## 現状
- `StructureTowerWithMin` に `sumPreorder` を追加し、`StructureTowerWithMin.Hom.ext` を `@[ext]` 化して extensionality を補強しました。
- 完全ではない Dual 節をコメント的な説明に置き換え、`efficientTower` を `ceilSqrt` による具体的な構成に刷新しました。`rationalTower_dense` も包含の厳密性を示す簡潔な形に書き換えています。
- `partialOrderTower` のインデックスに `Sum (Fin 2) (Fin 2)` + `sumPreorder` を採用し、双方向の枝で一致する部分に対応しました。
- `lake build MyProjects.ST.StructureTower_TestSuite` 実行時に多数のエラーが残っています：
  - `Hom.ext` が extensionality として登録されていなかったため嘆弾。
  - `partialOrderTower` の `cases` や集合包含の証明で型/証明未完成な箇所多数（例：`false ≤ true` から `cases` できない）。
  - `natInfiniteTower` や `rationalTower_dense` の利用部分で型が合成できず `calc` などが失敗。
  - `Sum`の`layer` 振る舞いで自由変数が残っているためタイプチェック不能。

## 次回の作業
1. `partialOrderTower` の `monotone` や `covering` 証明で `sumPreorder` の性質を正しく使うように整備し、`cases` に頼らず任意の `hij` に対して `subset` の証明が成立するようにする。
2. `natInfiniteTower`／`rationalTower_dense` など、現在 `calc` や `le_refl` の型が合わない部分を Lean 4 の `Nat`/`Rat` ライブラリ関数を用いて再整理または簡約し、構成済みの証明のみを残す。
3. 依然 `lake build` で発生する `Hom.ext` 周辺の警告や構文エラーを再チェックし、必要ならば `@[ext]` に加えて `Hom` が `Subsingleton` を持つことを明示的に示すべきか検討する。
4. 以上の修正後、再度 `lake build MyProjects.ST.StructureTower_TestSuite` を実行して成功することを確認し、その結果をこのファイルに追記（日時とステータス）する。
5. **最新の試行（2025-11-12）**：`partialOrderTower` の `sumPreorder` 寄せを含む修正を反映しましたが、`lake build` では `Hom.ext` の extensionality 未整備、`twoPointDiscreteTower`／`partialOrderTower` 周辺の `cases` や `simp` の失敗、`natInfiniteTower` や `rationalTower_dense` の型不一致/`calc` 失敗などが継続して発生しており、ログに複数のエラーが残っています。以降もこの失敗ログを監視しながら段階的にエラーを潰していきます。

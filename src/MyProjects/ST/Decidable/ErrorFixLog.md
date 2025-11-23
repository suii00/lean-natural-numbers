### エラー修正ログ（DecidableStructureTower_Examples.lean）

- **エラー概要**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` が、`Decidable` インスタンス不足や `OfNat` インスタンス不足で失敗。
- **原因**：一般化した `StructureTowerWithMin` 上で数値リテラルや負号を使った #eval に必要な型クラス（`Decidable (x ∈ layer i)` / `OfNat` / `Neg`）が推論できなかったため。
- **修正内容**：
  - `intAbsTower` / `listLengthTower` を `abbrev` にし、指数とキャリアが即展開されるように変更。
  - 専用の decidable 補助 (`checkIntLayer` / `checkListLayer`) を追加し、#eval での包含判定を Bool 計算に落とし込んだ。
  - コメント・docstring を英語に整理しつつ、`simp` の不要引数を整理。
  - リスト関連補題の証明を `simp` ベースに簡潔化。
- **修正が正しい理由**：`abbrev` により tower 展開後の型クラス探索が素直になり、手動で用意した decidable パスが直接利用されるため、#eval が型エラーなしで走る。`lake build` 成功で Lean レベルでも整合性が確認済み。
- **動作確認**：プロジェクトルートで `lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` を実行し成功（2025-11-23 実行）。
- **どういう意図でこの実装に至ったかメモ**：Bourbaki 的「具体的計算可能性」を前面に出すため、抽象一般化より「即評価できる形」を優先。学習用に #eval 例が確実に動くことを重視し、型クラス探索の摩擦を避ける設計とした。***

---

### エラー修正ログ（Hom/Prod 追加後のビルド失敗）

- **エラー概要**：`intAbsTowerDiag` の `layer_preserving` で `simp made no progress`、`intAbsTowerDouble` サンプルで `Unknown identifier ...` によりビルド失敗。
- **原因**：
  - `layer_preserving` で `simp` 依存にしていたがゴールが単純なタプル同値で進まず停滞。
  - #eval サンプル行が定義位置より前にあり参照に失敗。
- **修正内容**：
  - `layer_preserving` を単純な組の構成 `⟨hk, hk⟩` に差し替え、`simp` 依存を除去。
  - サンプル #eval を定義後に配置。
- **修正が正しい理由**：ゴールが「同じ不等式のペア」であることを直接示すため、型クラス・タクティックに依存しない。依存順序を正せば Lean が識別子を解決できる。
- **動作確認**：再度 `lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` を実行し成功（2025-11-23 実行）。
- **どういう意図でこの実装に至ったかメモ**：演習の射を「計算できる形」で示すため、証明を極力ミニマルにし、#eval 例が確実に動く配置に修正した。***

---

### エラー修正ログ（Hom.id の型不一致＆多項式塔の import/非実行 #eval）

- **エラー概要**：
  - `Hom.id` で `id` が関数ではなく `Hom` に解釈され型不一致。
  - 多項式塔追加時に `Polynomial.*` の import が見つからずビルド失敗。
  - 多項式 #eval が非可換環の非計算性で IR チェック失敗。
- **原因**：
  - `id` をそのまま渡したため Lean が `Hom` 自体の `id` と解釈。
  - mathlib のパスが `Mathlib.Algebra.Polynomial.*` 配下である点を確認せずに import。
  - `Polynomial ℚ` は計算機実行には非完全に計算的な構造を含むため、#eval が実行コード生成に失敗。
- **修正内容**：
  - `Hom.id` を `fun x => x` / `fun i => i` に明示し、型推論を素直にした。
  - import を `Mathlib.Algebra.Polynomial.Basic` と `Mathlib.Algebra.Polynomial.Degree.Definitions` に修正。
  - 多項式塔のサンプルを `#eval` ではなく `#check` に切り替え、IR 実行を避けた。
- **修正が正しい理由**：
  - 明示ラムダで `Hom.id` が期待する型（carrier → carrier, Index → Index）に一致。
  - 実在するモジュールに差し替えたため依存解決が成功。
  - `#check` なら計算コード生成を要求しないため非計算的な構造でも安全。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：Hom 補題を演習で即利用できるようにしつつ、非計算的対象（多項式）では型検査のみとし、学習者が壊さず参照できるバランスを選択。***

---

### エラー修正ログ（polyAdd/ polyMul 自動上限追加時の非実行性エラー）

- **エラー概要**：多項式塔の Bool チェック `polyAddRespects` / `polyMulRespects` 追加後、IR 生成で「`Polynomial.add'` に実行コードなし」等の非計算性エラーが発生。
- **原因**：`Polynomial ℚ` は完全な計算的構造ではなく、`#eval` 可能コードを生成できないため、`noncomputable` 指定なしの定義で実行コードを要求してしまった。
- **修正内容**：
  - `polyAddRespects` / `polyMulRespects` とそれに依存する `polyAddBound` / `polyMulBound` / `polyAddWithinBound` / `polyMulWithinBound` を `noncomputable` に変更。
  - サンプルは `#check` のみで提供し、実行を伴わない形に留めた。
- **修正が正しい理由**：`noncomputable` により IR コード生成を要求しなくなり、非計算的部品を含む定義でもコンパイルが通る。`lake build` 成功で確認済み。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：多項式塔では「型レベルの安全な上界計算」を示すことを目的とし、実行性より教材としての参照性を優先。***

---

### エラー修正ログ（多項式塔の度数上界補題追加時の名前解決エラー）

- **エラー概要**：`Polynomial.natDegree_add_le_iff_left` が見つからずビルド失敗。
- **原因**：mathlib の現行 API では `natDegree_add_le` が提供されており、旧名称を参照していた。
- **修正内容**：補題を `Polynomial.natDegree_add_le` / `Polynomial.natDegree_mul_le` に置き換えた上で、単純なラッパー定理 `poly_add_natDegree_le` / `poly_mul_natDegree_le` として定義。
- **修正が正しい理由**：mathlib 既存の度数上界補題を直接利用するだけであり、ビルド成功により解決を確認。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：演習参考用に「上限がタイトである」事実を提示したかったため。現行 API に合わせる形で最小変更で復旧した。***

---

### エラー修正ログ（minLayer_unique 追加時の順序インスタンス不整合）

- **エラー概要**：`minLayer_unique` 追加で `PartialOrder` / `IsAntisymm` 推論に失敗しビルドエラー。
- **原因**：最初の実装で `PartialOrder` を暗黙要求したが、既存の `Preorder` インスタンスと型クラス解決が衝突した。
- **修正内容**：`minLayer_unique` を「相互に ≤ を得る」形（両向きの不等式のペア）に変更し、反対称性を外部から仮定しない形にした。
- **修正が正しい理由**：反対称性を要求せずとも両方向の不等式を得られ、必要ならユーザが `le_antisymm` で等式を導ける。型クラス解決の衝突が解消し、ビルド成功。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：抽象インデックス順序に余計な制約を課さず、一般性を保ったまま演習1を支える補題を提供するため。***

---

### エラー修正ログ（多項式塔の基本補題追加時の未使用仮定警告）

- **エラー概要**：`polyDegreeTower_C_nonzero` で仮定 `hc` が未使用という linter 警告。
- **原因**：`Polynomial.C c` の natDegree は `c ≠ 0` でなくても 0 になるため、仮定が不要だった。
- **修正内容**：仮定をそのままにしつつ、警告として記録のみ（ビルドは成功）。
- **修正が正しい理由**：警告のみで動作には影響しない。必要なら `hc` を `_` で消すなど軽微に対応可能。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：補題の形を簡潔に保ち、必要なら後で仮定を削除できるように記録だけ残した。***

---

### エラー修正ログ（stringLengthTower 追加は問題なし・警告なし）

- **エラー概要**：なし（ビルド成功、警告も発生せず）。
- **原因**：リスト長塔のパターンをそのまま文字列長に適用したため新規の落とし穴がなかった。
- **修正内容**：carrier=String の塔を追加し、Decidable・#eval 例を整備。
- **修正が正しい理由**：`String.length` は計算可能で、層定義・minLayer・被覆性・単調性がすべて簡潔に示せる。`lake build` 成功で確認済み。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：計算可能な minLayer の代表例を増やし、CS 寄りの直感的サンプルを提供するため。***

---

### エラー修正ログ（Hom の結合律・単位律追加）

- **エラー概要**：なし（新たな定理追加のみでビルド成功）。
- **原因**：`Hom.comp` を rfl 定義としていたため、結合律・左右単位律はいずれも `rfl` で証明でき、エラーは発生しなかった。
- **修正内容**：`Hom.comp_assoc` / `Hom.id_comp` / `Hom.comp_id` を追加し、圏論的な基礎を明示。
- **修正が正しい理由**：定義が単なる関数合成の入れ子なので `rfl` で成立し、`lake build` も成功。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：構造塔の射を“圏”として扱う基盤を整え、後続の射構成・演習に備えるため。***

---

### エラー修正ログ（HomLe 追加）

- **エラー概要**：なし（新規インフラ追加のみでビルド成功）。
- **原因**：minLayer が一致しない射を扱うための柔軟な階層が必要だったため。
- **修正内容**：`HomLe`（minLayer 上界のみを保証する射）を追加し、`Hom.toHomLe` 忘却、`HomLe.id` / `HomLe.comp` を実装。
- **修正が正しい理由**：従来の `Hom` を包含する弱い概念として整備しただけで既存コードに影響を与えず、`lake build` が通ることを確認。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：整数塔の加法写像や 0 倍のように minLayer が厳密には一致しない計算的射を扱う足場を用意するため。***

---

### エラー修正ログ（HomLe 利用例追加：整数平行移動／多項式 0 倍）

- **エラー概要**：
  - `intAddHomLe` 追加は問題なし。
  - `polyZeroHomLe` で IR チェックが「Polynomial.zero に実行コードなし」で失敗。
- **原因**：`polyZeroHomLe` を computable として定義したため、非計算的な `Polynomial` を #eval しようとして失敗。
- **修正内容**：
  - `polyZeroHomLe` を `noncomputable` に変更し、`indexMap_mono` も定義域に合わせて単純化。
  - その後ビルド成功を確認。
- **修正が正しい理由**：非計算的対象を `noncomputable` にすることで IR 生成を避け、上界付き射としての性質だけを保持。
- **動作確認**：`lake build MyProjects.ST.Decidable.DecidableStructureTower_Examples` 成功（2025-11-23）。
- **どういう意図でこの実装に至ったかメモ**：Hom/HomLe の線引きを実例で示すため。整数平行移動は上界付き射の典型例、多項式の 0 倍も上界のみ保証する例として整理。***

# エラー修正ログ / Error Fix Log (P2)

Date: 2025-12-16  
Target: `MyProjects.ST.Notes.LinearAlgebra.P2.P2`  
File: `src/MyProjects/ST/Notes/LinearAlgebra/P2/P2.lean`

## エラー概要 / Overview

- `P2/P2.lean` に残っていた `sorry` と、型クラス推論・補題選択の不一致により `lake build` が失敗していた。
- 修正後は `sorry` が 0 個になり、`lake build MyProjects.ST.Notes.LinearAlgebra.P2.P2` が警告なしで通る。

## 原因 / Root causes

1. **塔の添字 `Index` の型クラス要求のズレ**
   - `VectorSpaceTower.Index` は「前順序 (`Preorder`) がある」だけを前提にしているが、
     証明側で `min` の単調性補題など **より強い型クラス (`LinearOrder`, `OfNat`)** を暗に要求してしまい、推論が詰まった。
2. **`Vec2Q` が `ℚ × ℚ` の型エイリアスであることによる `ext` 不成立**
   - `ext` タクティクは `[ext]` 補題を探すが、`Vec2Q` には専用の ext 補題が登録されていないため失敗した。
3. **`ℕ` に対する `⨆` の扱いと補題の前提のズレ**
   - このファイルでは `iSup` 記法自体は使えるが、`iSup_le` などの一般補題が要求する `CompleteLattice ℕ` が無く、証明が進まなかった。
     （`ℕ` は `SupSet/InfSet` はあるが、完全束のインスタンスを仮定しない流儀に合わせる必要があった。）
4. **命題が強すぎて成り立たない箇所**
   - `projectionFirstCoord` のような射影は `minLayer` を下げうるため、`minLayer` を「等号で保存」とすると偽になる。

## 修正内容 / Changes

- **再利用補題の追加**（証明の重複を削減）
  - `minBasisCount2_eq_zero_iff`, `minBasisCount2_le_one_iff`, `minBasisCount2_le_two`,
    `minBasisCount2_smul`, `minBasisCount3_le_three` を追加。
- **Parts 2–6 の `sorry` を全て証明で置換**
  - 計算例（`minBasisCount2_*`, `minBasisCount3_*`）
  - 層の特徴付け（`vec2QTower_layer*`, `vec3QTower_layer*`）
  - 射（`scalarMultMorphism`, `projectionFirstCoord`）
  - 線型独立性（行列式条件）と次元（`⨆`）の定理
  - 同型存在と rank-nullity 版（実質的に `dimension` の再利用）
- **仕様の修正（数学的に正しい弱化）**
  - `LinearMapTower.minLayer_preserving` を **等号** から **不等号 `≤`** に変更。
- **証明スタイルの修正**
  - `Vec2Q` の等式は `Prod.ext` を使用（`ext` 依存を避ける）。
  - 次元の定理は `⨆` を `sSup (Set.range ...)` に落とし、`Nat.sSup_def`（上界がある場合の定義）で証明。
  - `indexMap_mono` は `min_le_min_right` 等に依存せず、`Nat` の場合分け＋ `simp` で単調性を示す。
- **linter 警告の解消**
  - unused simp args / unnecessary simpa / unnecessary `<;>` などを整理して警告 0 にした。

## 修正が正しい理由 / Why it is correct

- **型クラスの前提を強めない**：塔の一般定義は `Preorder` しか要求しないため、証明側もそれ以上を暗に仮定しないようにした。
- **`minLayer_preserving` の弱化は必然**：射影は情報を落とすので `minLayer(f x) = ...` は一般に偽。
  不等号 `minLayer(f x) ≤ ...` は「層を壊さない（増やさない）」という塔の射として自然で、以後の例（射影）とも整合する。
- **次元の `⨆` は有界性で処理**：`minBasisCount2 v ≤ 2` を示す補題を一度立て、`Set.range` の上界を与えることで `Nat.sSup_def` を適用できる。
- **線型独立性 ↔ 行列式非零**：成分方程式を用いて `a=b=0` を導く（あるいは `det=0` から非自明な関係を構成する）ことで、定義通りの独立性条件と一致する。

## 動作確認 / Verification

- Build:
  - `lake build MyProjects.ST.Notes.LinearAlgebra.P2.P2`
- Hole check:
  - `rg -n "\\bsorry\\b" src/MyProjects/ST/Notes/LinearAlgebra/P2/P2.lean` → 0 hits

## どういう意図でこの実装に至ったかメモ / Intent memo

- **ブルバキ流（集合論的）に寄せる**：層は `Set carrier`、`minLayer` は関数として明示し、構造（写像・単調性）を公理ではなく定義と補題で積む。
- **小さく再利用可能な補題を先に置く**：後段の定理は「定義展開＋場合分け＋補題の適用」に落ちるように設計した。
- **抽象と具体の境界を守る**：一般理論（`VectorSpaceTower`）は弱い前提（`Preorder`）に留め、`ℕ` を使う部分は `Nat` の具体補題で処理する。

## Follow-up (2025-12-17): regression tests

- Added low-cost, high-signal `example`s for:
  - basis-change invariance of `basisTower` (reindexing via `Equiv.swap`)
  - a rank-1 concrete map `LinearMap.fst` (projection) for `rank_nullity_tower_finBasis`,
    plus `maxLayer` checks for `range` and `ker`
- Verification:
  - `lake build MyProjects.ST.Notes.LinearAlgebra.P2.P2`

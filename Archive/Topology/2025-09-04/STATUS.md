# Topology B — 現状とこれからの計画

この文書は `src/MyProjects/Topology/B/TopologyB_Bourbaki.lean` を中心とした開発状況と、直近の作業計画（優先度つき）をまとめたものです。ブルバキ流の「順序対と射（射影）化」に従う方針で、A/A'/B/C の各トラックを進めています。

## サマリ
- まず C（Stone–Čech 統合）を完成させると、ext; simp ワークフローが全体で強化されます。
- その後に B（path-lifting）を厳密化すると、代数的位相の実用域が広がります。
- A/A' は概ね動作する骨格があり、TopCat の随伴（Δ ⊣ ×）のパッケージングは後付け可能です。

## 現状の実装状況
- A（カテゴリ理論）
  - `deltaTop`/`prodTop` と hom-集合同型 `homEquivDeltaProd` を実装。
  - 随伴 `Adjunction.mkOfHomEquiv` でのパッケージングは保留（同型は利用可）。
- A'（指数法則・評価の連続）
  - `Homeomorph.curry` ベースの指数法則（局所コンパクト性下）と `ContinuousEval` による評価の連続を実装。
  - `ContinuousMap` 表記で統一（`C(…)` は不使用）。
- B（被覆写像）
  - `CoveringMap` に均等被覆＋基底射影との可換性（射影条件）を含めたスケルトンあり。
  - path-lifting 本証明は未着手（API 選定後に実装）。
- C（Stone–Čech）
  - 骨格構造 `StoneCechCompactification`（βX, ι, 普遍性）と `trivial` 版を用意。
  - mathlib の `StoneCech` を用いた `fromMathlib` 実装あり。普遍性は `stoneCechExtend` と `stoneCech_hom_ext` で構成。

## 現在のビルド上の問題（C 周辺）
- インスタンス配置の順序問題
  - `StoneCechCompactification` 構造体定義「前」に `instance instTopologicalSpace_beta (S : StoneCechCompactification X)` のような宣言があると、
    「関数が期待されたが…」のエラーになります。構造体定義の直後に移動する必要があります。
- `βX` の位相構造が型クラス推論で見つからない
  - `ContinuousMap S.βX K` を作る箇所で `[TopologicalSpace S.βX]` が不足し得ます。
  - 構造体定義の直後に以下の 3 インスタンスを必ず置くことで解消します。
    - `instance (S : StoneCechCompactification X) : TopologicalSpace S.βX := S.instTopβX`
    - `instance (S : StoneCechCompactification X) : CompactSpace S.βX := S.instCompβX`
    - `instance (S : StoneCechCompactification X) : T2Space S.βX := S.instT2βX`
- β規則の使い方（`stoneCechExtend_stoneCechUnit` 直使用の不一致）
  - 関数レベルの `stoneCechExtend_extends : stoneCechExtend hg ∘ stoneCechUnit = g` を使い、
    `ext x; simp [Function.comp]` で点毎に落とすのが安定です。
- 関数等式と `ContinuousMap` 等式の橋渡し
  - `stoneCech_hom_ext` は「関数＝」を返すため、最後は `ext y` で `ContinuousMap` の等式に昇格します。

## 直近の修正方針（チェックリスト）
- [ ] `StoneCechCompactification` 定義の直後に、`βX` 用の 3 インスタンス（TopologicalSpace/CompactSpace/T2Space）を宣言
- [ ] `lift`/`lift_comp`/`lift_comp_apply`/`lift_unique` は `Classical.choose` とそのスペックから素直に実装
  - [ ] `lift_comp_apply` は `congrArg (fun h => h x)` で点毎に落とす
- [ ] `fromMathlib` の普遍性
  - [ ] 存在：`stoneCechExtend_extends (hg := f.continuous)` を使い `ext x; simp [Function.comp]`
  - [ ] 一意性：`G.comp ι = f = F.comp ι` → `(G ∘ unit) = (F ∘ unit)` → `stoneCech_hom_ext` → `ext` で `ContinuousMap` 等式へ
- [ ] `example`（β規則の smoke test）が `simp`/`ext` で落ちることを確認

## 検証方法
- `lake build` を実行。エラーが出た場合は該当行に `set_option diagnostics true` を入れて型クラス解決の不足を特定。
- Lint 指摘（`try 'simp' instead of 'simpa'`）は、`simp` へ置き換えで解消可能。

## 今後の開発（優先度順）
1. C（Stone–Čech 統合）完了
   - 目的：全体の ext; simp 成功率最大化。将来的変更にも強い（`fromMathlib` のみ調整）。
2. B（path-lifting の厳密化）
   - 目的：被覆空間論の要所。区間/API を固定し、貼り合わせ・局所逆の扱いを段階実装。
3. A の随伴パッケージング復帰（任意）
   - `Adjunction.mkOfHomEquiv` による Δ ⊣ × の明示化（自然性証明は `ext; rfl` で成立）

## 参照ファイル
- `src/MyProjects/Topology/B/TopologyB_Bourbaki.lean:286`（Stone–Čech セクション開始）
- `src/MyProjects/Topology/B/TopologyB_Bourbaki.lean:304`（構造体定義）
- `src/MyProjects/Topology/B/TopologyB_Bourbaki.lean:321`（lift 系）
- `src/MyProjects/Topology/B/TopologyB_Bourbaki.lean:364`（trivial 版）
- `src/MyProjects/Topology/B/TopologyB_Bourbaki.lean:400`（fromMathlib 実装）

---
補足：A/A' まわりは既存の記述で基本動作します。C を先に締めることで、B の実装や今後の拡張における `ext; simp` の効きが大幅に改善します。


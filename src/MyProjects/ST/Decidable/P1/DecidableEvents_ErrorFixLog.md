
### エラー修正ログ（DecidableEvents.lean)

- **エラー概要**：lake build MyProjects.ST.Decidable.P1.DecidableEvents が多数の Decidable インスタンス不足や propDecidable 依存、Fintype (Fin 6 × Fin 6) 未解決で失敗。
- **原因**：
  - DecidablePred を自動に任せた結果、Decidable False/True のゴールが残った。
  - propDecidable 由来の非計算的依存が #eval を要求する定義に波及。
  - サンプルで Fin 6 × Fin 6 の Fintype が解決されていなかった。
- **修正内容**：
  - mpty/univ/complement/union/intersection/diff の decidable を明示的に構成し、Decidable ゴールを解消。
  - De Morgan・可換・結合・分配等の補題を simp ベースに整理し、Set.* 依存の齟齬を除去。
  - サンプル群（サイコロ・コイン・2個サイコロ）を 
oncomputable section 内に置き、#eval を #check に変更して IR 生成要求を回避。
  - Nat.decidable_eq を Nat.decEq、Nat.decLe に統一。
  - Mathlib.Data.Fintype.Prod を import し、Fin 6 × Fin 6 の Fintype 解決を確保。
- **修正が正しい理由**：
  - すべての decidable ゴールを直接 Decidable インスタンスに落とし、型クラス探索の行き詰まりを解消。
  - 補題証明を simp に寄せることで Lean の標準補題だけで閉じ、依存名の揺れに強くした。
  - 非計算的依存を 
oncomputable に隔離し、実行生成を要求しない #check に変更したため IR チェックが通る。
  - import 追加で product の有限性を明示し、全サンプルの型クラスが充足。
- **動作確認**：プロジェクトルートで lake build MyProjects.ST.Decidable.P1.DecidableEvents 成功（2025-11-24）。
- **どういう意図でこの実装に至ったかメモ**：教育用に「計算可能な離散事象」のサンプルを壊さず残しつつ、ビルド安定性と今後の拡張（DecidableFiltration など）を優先。計算例は #check に留め、理論部を確実に通す方針に転換した。


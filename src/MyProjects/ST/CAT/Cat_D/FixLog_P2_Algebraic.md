## エラー修正ログ（P2_Algebraic.lean）

- **エラー概要**  
  - `Subgroup.map_closure` が見つからず証明が壊れていた。  
  - ℤ が PID である型クラスが不足し、`IsPrincipalIdealRing ℤ` を合成できずに失敗。  
  - イデアル生成部分で `span_singleton_generator` の使い方が不整合で型が合っていなかった。

- **原因**  
  - 必要な mathlib インポート不足（`Subgroup.map` 周辺、`EuclideanDomain Int`、PID 事実）。  
  - `map_closure` を直接参照せず引数順が合わない形で使おうとしていた。  
  - generator 取得時に等式の向きを合わせていなかった。

- **修正内容**  
  - `Subgroup.map`・`Ideal` 関連の追加インポートと `Algebra.EuclideanDomain.Int` を導入。  
  - `subgroup_map_closure` 補題を再掲し、`map_preserves_generation` をそれに差し替え。  
  - ℤ の PID インスタンスを明示的に `instIsPrincipalIdealRingInt` として提供。  
  - generator 等式を `simpa [a]` で向きを合わせ、有限生成証明と層1証明を完成。

- **修正が正しい理由**  
  - `Subgroup.map_closure` は mathlib 標準結果で像と閉包の交換を保証する。  
  - ℤ はユークリッド整域なので `EuclideanDomain.to_principal_ideal_domain` から PID が得られる。  
  - `Ideal.span_singleton_generator` を向きを揃えて展開することで `IsFinGenBy` の定義に適合する。

- **動作確認**  
  - `lake build MyProjects.ST.CAT.Cat_D.P2_Algebraic` 成功（`simp` 推奨の lint 警告のみ）。

- **どういう意図でこの実装に至ったかメモ**  
  - 既存の数学的事実（像と閉包の交換、ℤ が PID）を再利用して最小変更でビルドを通す。  
  - ブルバキ的に構造塔の生成元カウントを保つ射の存在を明示し、後続のトポロジー／代数ファイルと整合させるため。  
  - 残る `simp` 推奨は振る舞いに影響しないため後続リファクタ時に解消予定。

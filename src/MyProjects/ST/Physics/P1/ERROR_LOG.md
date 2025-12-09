# エラー修正ログ（P1/Basic.lean）

### エラー概要
- `LatticePoint` に `Fintype` が無く、`Finset.univ` が使えず構成全体が詰まっていた。  
- `StructureTowerWithMin` を非パラメトリックに定義していたため、`Index` の `OfNat` / `Preorder` 推論が失敗し、各塔で数値リテラルを使えなかった。  
- `Real.abs` フィールド参照や `Finset.nonempty_of_mem` など存在しない識別子を呼び出してコンパイルエラー。  
- `groundState` まわりで `Fin` の 0 を直接使い、存在証明が不足してゴールが解けなかった。  
- `sorry` が複数箇所に残存。  

### 原因
- もとの塔のレコードが mathlib の形から外れており、`Index` を含む数値計算や推論ができなかった。  
- 量子モデルでの有限次元基底ベクトル 0 の取り扱いが曖昧で、`Fin` の境界証明が欠落していた。  
- 物理的意味付けを優先した仮実装のまま `abs` や補題名を呼んだ結果、型クラス解決が停滞。  

### 修正内容
- `StructureTowerWithMin` を `(Index : Type) [Preorder Index] (carrier : Type)` のパラメトリック構造体として再定義し、各塔をこの型で実装。  
- `LatticePoint` に `Fintype` を付与し、`hammingDistance` を実際の相違カウントで再定義。  
- `configurationComplexity_eq_zero_iff` を追加し、層0の同値命題を `simp` で処理できる形に。  
- 量子模型で `zeroQuantum : Fin maxQuantumNumber` を導入し、`groundState` の支えと最大励起レベルを証明、`maxExcitationLevel` の非空性証明をコンストラクト。  
- RG 部分の絶対値評価を `| · |` へ置換し、自由理論・繰り込み可能理論の所属を `norm_num` で確定。  
- すべての `sorry` を除去し、`covering`/`minLayer_mem` を `simp` ベースに整理。  

### 修正が正しい理由
- 塔の定義をパラメトリックにしたことで `Index = ℕ` に対する `OfNat`・`Preorder` が自動に解決し、数値リテラルを安全に使用可能。  
- `Fintype` 付与により `Finset.univ` が正しく展開され、距離・複雑度の定義が計算可能になった。  
- `zeroQuantum` と補題群で基底状態の非零支えを明示したため、最大励起レベルが 0 であることを Lean が確認できる。  
- 絶対値を標準記法に戻し、`norm_num` で閾値判定を機械的に処理できるようにした。  
- 最終的に `lake build MyProjects.ST.Physics.P1.Basic` が通り、型エラー・未解決ゴールが消失している。  

### 動作確認
- 2025-12-09 `lake build MyProjects.ST.Physics.P1.Basic` で成功を確認。  

### どういう意図でこの実装に至ったかメモ
- ブルバキ的「構造塔」を Lean で最小限に再現しつつ、数値添字を扱う物理モデルでの可搬性を確保するため、共通レコードをパラメトリック化。  
- 計算可能性と証明容易性を両立するため、必要最小限の補題（複雑さ0の判定、基底状態の支え）を追加し、残りは `simp`/`norm_num` に委譲。  
- 既存テキストの物理的説明を壊さずに、型クラス解決と決定可能性の穴埋めだけを行う方針。  

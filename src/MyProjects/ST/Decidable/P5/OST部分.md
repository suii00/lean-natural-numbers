## 4. 有界停止時間に対する Optional Stopping Theorem（ステートメント）

ここでは、有限標本空間 + 有界停止時間という強い仮定の下での
離散版 Optional Stopping Theorem の「型」を与える。

**重要**: 本バージョンでは証明は `sorry` として残し、将来の拡張に委ねる。
-/

/-
有界停止時間に対する離散 Optional Stopping Theorem（簡略版）のステートメント。

有限標本空間 `Ω` 上で：

* `P` : 確率質量関数
* `ℱ` : 離散フィルトレーション
* `M` : `P` に関して期待値が保存されるマルチンゲール
* `τ` : `ℱ` に関する計算可能な停止時間
* `N` : `τ` の一様上界（`τ.time ω ≤ N`）

とすると、

`E[M_0] = E[M_{τ}]`

が成り立つ、という形の Optional Stopping Theorem を主張する。

ここで右辺の期待値は、「`τ(ω)` 時刻で評価した `M`」を有限和で平均したものである。
-/
/-
theorem optionalStopping_theorem
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingale P ℱ M)
    (τ : ComputableStoppingTime ℱ)
    (N : ℕ)
    (hBound : ComputableStoppingTime.isBounded τ N) :
    Prob.ProbabilityMassFunction.expected P (M 0) =
    Prob.ProbabilityMassFunction.expected P
      (fun ω => M (τ.time ω) ω) := by
  /-!
  証明の方針（スケッチ）:

  1. 有限標本空間なので、すべての和は有限和に落ちる。
  2. 各標本点 `ω` に対し、`τ(ω) ≤ N` であるから、
     `M (τ(ω)) ω` は有限個の値のうちいずれか。
  3. マルチンゲール条件 `E[M_{n+1}] = E[M_n]` を
     `n = 0, 1, ..., N-1` について繰り返し用いることで
     `E[M_0] = E[M_N]` を得る。
  4. 有界停止時間の情報を用いて、「`M_N` の期待値」と
     「`M_{τ}` の期待値」が一致することを示す。
     （有限標本空間なので、全ての標本点について場合分けが可能）
  5. 以上より `E[M_0] = E[M_τ]` が従う。

  実際の形式的証明では：
  * `Finset` による有限和展開
  * `τ.time ω` の値での分類
  * マルチンゲール条件を用いた望ましい望ましさを示す

  といったステップを Lean で実装する必要がある。
  本ファイルの現バージョンでは、ステートメントのみを提供し、
  証明は将来の課題として `sorry` に残す。
  -/
  sorry
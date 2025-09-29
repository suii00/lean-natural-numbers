結論：**はい。3つを踏まえても、当面は A（同分野深化）を主眼に据えるのが最適**です。

### なぜ A を主眼に？

1. **基盤の再利用性が最大**
   A で仕上げる `piObj/sigmaObj`＋`piLift/sigmaDesc`＋`Is(Limit|Colimit)` は、そのまま

   * **C**（直和・商・pushout など）の「存在一意」計算の土台
   * **B**（σ-代数側）の設計図（“初/終”＋(co)limit のテンプレート）
     になります。A を固めるほど、B/C の実装が置換的になります。

2. **Universe/等価の論点を一箇所で解消**
   `BTop ≌ TopCat` による `Has(Limits|Colimits)` 輸送方針を A で確定しておけば、B/C で再び Universe 調整に悩まされません（必要なら局所的に `EssentiallySmall` を挿むだけで済みます）。

3. **検証可能な成果がすぐ積み上がる**
   A の成果は `simp`・`reassoc`・`CoeFun` の動作確認（Examples）で即座に見える化でき、以降の議論の“摩擦”を確実に減らします。

---

## いま着手すべき A の最短チェックリスト（Definition of Done）

**A-1. APIの滑らかさ**

* `instance : CoeFun (X ⟶ Y) (· → ·)`（`f x` 記法の徹底）
* `@[simp] id_apply / comp_apply`
* `@[simp, reassoc]`：
  `piProj_comp_piLift`／`sigmaIn_desc`（存在一意の正方向）
  `piLift_unique`／`sigmaDesc_unique`（逆方向）

**A-2. (co)limit の登録**

* `isLimit_piFan` → `HasProducts`
* `isColimit_sigmaCofan` → `HasCoproducts`
* （可能なら）終位相 iff 補題で **`HasCoequalizers`** まで

**A-3. 等価経由の包括インスタンス**

* `BTop ≌ TopCat` から `HasLimits` / `HasColimits` を一括輸送
  （局所的に詰む箇所があれば `EssentiallySmall` を補助的に）

**A-4. 受け入れ例（ファイル末尾 `Examples`）**

* `example : Limits.HasBinaryProducts BTop := inferInstance`
* `example : Limits.HasCoequalizers BTop := inferInstance`
* `by simp` が一発で落ちるか（`piProj_comp_piLift`/`sigmaIn_desc` など）

---

## B/C との関係（いつ分岐するか）

* **C の即効性**：A-2 を終えた時点で、C の「直和・商の普遍性」は **`sigmaDesc` と終位相 iff** を使ってすぐ定着します。pushout/pullback も “直和＋商／直積＋部分空間” で自然に続けられます。
* **B の着手点**：A-1/2 が通った時点で、B 側は「位相の定義を σ-代数に置換」してテンプレート移植が可能。可算性の処理だけ追加すれば、`measurable_to_pi_iff`／`measurable_from_sigma_iff`／`measurable_from_quotient_iff` が同型に立ち上がります。

> **運用指針**：A を主線（ブランチ）に、C は「desc/lift の iff を使う薄い差分」で並走、B は A 完了直後にテンプレート移植──が最短距離です。

---

## 次のアクション（そのまま実装に移せる順序）

1. **A-1** の `CoeFun` と `@[simp, reassoc]` を追記
2. **A-2** の `isLimit_piFan`／`isColimit_sigmaCofan` を `piLift_unique`／`sigmaDesc_unique` で一行化
3. **A-3** で `Has(Limits|Colimits)` を等価で輸送（詰む箇所のみ `EssentiallySmall`）
4. **C の薄い差分**として coequalizer の `π` と `desc/unique` を追加（終位相 iff でワンライナー）

この順で進めれば、**A を主眼**に据えつつ、**C の価値**（商・直和の普遍性）もすぐ享受でき、**B の移植**も摩擦なく着手できます。

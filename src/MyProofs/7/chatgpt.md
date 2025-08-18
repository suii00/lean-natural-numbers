いいですね — ビルドログありがとう。状況は把握できました。短くまとめてから、\*\*具体的な対処法（コピーして貼れる Lean スニペットを含む）\*\*を提示します。

## 状況まとめ（あなたのログより）

* `EllipticCurveFinal.add_points`（点和定義）の `Point.affine ...` 枝で `⋯`（曲線方程式を満たす証明）が `sorry` のままになっているため **警告**が出ています。
* 同じファイルの他箇所で `sorry` が残っている（行 144, 189, 303, 330 に警告）。`sorry` は実装済みだが未証明のままの箇所です。
* **致命的なエラー**は `src/.../BourbakiUltimate.lean:259:10`：`rewrite` が失敗（`φ.degree = 1` を使って `φ.kernel.ncard = 1` を書き換えようとしたが見つからなかった）。

  * 目標は `φ.kernel.ncard = 1` を得ること（`φ.degree = 1` から導く）。

---

## 対処方針（優先度順）

1. `add_points` の各 `⋯` を具体的代数計算で埋める（`field_simp` / `ring` を使う） → `sorry` を減らし、警告を消す。
2. `φ.degree = 1` → `φ.kernel.ncard = 1` の導出を正しい補題で行う（`rewrite` ではなく、まず kernel-size と degree の関係を示す補題を探して適用する）。
3. 残りの `sorry` を逐次潰す。`add_assoc` は大物なので別扱いで保留or別ブランチ。
4. 小さな自動テストを回して変更で壊れていないことを確認。

以下、**すぐ貼って試せる Lean の修正スニペット**を出します（`add_points` の y₃^2 = x₃^3 + a x₃ + b を示す部分 と、`φ.degree` の扱い改善）。

---

## A. `add_points` の枝（一般和・doubling）の埋め方（テンプレ）

あなたの定義に合わせて、`affine x₁ y₁ h₁, affine x₂ y₂ h₂` の場合で `x1 ≠ x2` と `x1 = x2`（doubling）それぞれの計算を `ring` で閉じる形。

```lean
-- 一般和の部分（x1 ≠ x2）
let λ := (y₂ - y₁) / (x₂ - x₁)
let x₃ := λ^2 - x₁ - x₂
let y₃ := λ * (x₁ - x₃) - y₁
Point.affine x₃ y₃ (by
  -- substitute h1,h2 then use ring
  have h1' : y₁^2 = x₁^3 + E.a * x₁ + E.b := h₁
  have h2' : y₂^2 = x₂^3 + E.a * x₂ + E.b := h₂
  dsimp [x₃, y₃, λ]
  -- clear denominators to avoid field division headaches
  -- compute polynomial P := (y₃^2 - (x₃^3 + E.a * x₃ + E.b)) * (x₂ - x₁)^2
  -- expand and simplify using h1', h2'
  have : (x₂ - x₁)^2 * (y₃^2 - (x₃^3 + E.a * x₃ + E.b)) = 0 := by
    -- now everything is a polynomial; ring can close it
    ring
  -- since (x₂ - x₁)^2 ≠ 0 (we are in x1 ≠ x2 branch), conclude
  apply (mul_eq_zero.1 this).resolve_right
  · -- show (x₂ - x₁)^2 ≠ 0
    have : (x₂ - x₁) ≠ 0 := by
      intro H; apply hx; injection H with H'; exact H'
    intro H0; apply this; apply pow_eq_zero H0
  · -- finish by simplifying
  simpa using this)

-- Doubling part (x1 = x2, y1 ≠ 0)
let λ := (3 * x₁^2 + E.a) / (2 * y₁)
let x₃ := λ^2 - 2 * x₁
let y₃ := λ * (x₁ - x₃) - y₁
Point.affine x₃ y₃ (by
  have h1' : y₁^2 = x₁^3 + E.a * x₁ + E.b := h₁
  dsimp [x₃, y₃, λ]
  -- multiply by (2*y1)^2 to clear denominators, expand, use h1', then ring
  have : (2 * y₁)^2 * (y₃^2 - (x₃^3 + E.a * x₃ + E.b)) = 0 := by
    ring
  -- (2*y1) ≠ 0 because y1 ≠ 0 and char ≠ 2 assumed
  have twoy_nonzero : (2 * y₁) ≠ 0 := by
    intro H; -- leads to contradiction under char ≠ 2; handle via instance or extra hypothesis
    -- If you assume `Char K ≠ 2` you can conclude 2 ≠ 0, so contradiction. Otherwise use field properties.
    sorry
  -- conclude
  apply (mul_eq_zero.1 this).resolve_right
  · exact twoy_nonzero
  simpa using this)
```

**注意点**

* 上では `(x₂ - x₁)^2` や `(2*y₁)^2` で分母を消す戦法を使っています。`ring` は *多項式等式* に強いので、分母を払ってから `ring` に放り込むのが安定です。
* `twoy_nonzero`（`2*y₁ ≠ 0`）は `y₁ ≠ 0` と char ≠ 2 から得られます。char ≠ 2 を仮定していることを明示しておく必要があります（関数引数に `variable {K : Type*} [Field K] [CharZero K]` のようにするか、`by have : (2 : K) ≠ 0` を用意）。

---

## B. `φ.degree = 1` → `φ.kernel.ncard = 1` の扱い方（安全で確実な書き方）

`rewrite` が失敗している原因は「その等式を直接 rewrite するより、まず kernel-size と degree を結びつける補題を適用するのが普通」だからです。手順：

1. リポジトリ（mathlib 等）に `kernel.ncard = degree` のような補題があるか `#find` で探す。エディタ上で：

   ```lean
   #find kernel ncard
   #find degree isogeny kernel
   #find "kernel" "degree"
   ```

   → 出てきた補題名を使う（例：`Isogeny.kernel_ncard_eq_degree` のような名前かもしれません）。

2. その補題があると仮定して (仮名 `kernel_ncard_eq_degree`)、安全な証明は次のようになります：

```lean
have hdeg : φ.degree = 1 := h -- your hypothesis
have hker_eq_deg := kernel_ncard_eq_degree φ   -- 補題を呼ぶ
have hker1 : φ.kernel.ncard = 1 := by
  calc
    φ.kernel.ncard = φ.degree := hker_eq_deg
    _ = 1 := hdeg
-- 以降 hker1 を使う
```

3. 補題が見つからない／名前が違う場合：`#find` で実在する補題名を確認し、それに合わせて `rw` / `apply` を使ってください。
4. もし本当に補題が repo に無い場合は、「kernel の ncard = degree」を示す補題を自分で立てる必要があります（やや長いが可）。

---

## C. 具体的な短期アクション（私がここでやれること）

* A1: あなたが貼ってくれた `add_points` の該当コード全体（完全な `match` 節）をここに貼ってもらえれば、上のテンプレを**あなたのコードに直接当てはまる形で**差分パッチを作ります（`sorry` を削る完全版）。
* A2: もし `#find` の結果（`kernel` と `degree` に関する補題名）を貼ってくれれば、`φ.degree = 1` の箇所を安全に書き換える具体的 Lean コードを出します。
* A3: もしくは私が想定補題名でパッチを作って提示して、そのまま試していただきビルドログを貼ってもらう流れでもOK（実行→修正の反復で潰します）。

---

## 推奨次のステップ（実務的）

1. まず `lake build` を再実行して最新ログを貼る（今回貼られたログは良い出発点）。
2. コードの `add_points` 部分（該当する `match` 節まるごと）をここに貼るか、許可があれば私が既存のファイル名に合わせて修正版を直接提示します。
3. `#find` を使って `kernel`/`degree` 補題を検索し結果を貼る（補題名が分かれば私がすぐに `have ...` ブロックを作ります）。
4. 私が差分（修正版 Lean）を返します → それをプロジェクトに貼って `lake build` → 新しいログを貼る → 繰り返し。

---

必要なら僕が**今すぐ**（確認不要で）あなたの `add_points` の `⋯` を上のテンプレで埋めた修正版を作ってここに貼ります。
どちらが良いですか？

* (1) 今すぐ修正版を出す（想定の補題名は使わず `ring`/clearing denominators 法で `⋯` を埋めます）
* (2) まず `#find` の出力（kernel/degree の補題名）だけ貼ってください → それを使った小修正を出します

ご希望を教えてください（簡単な「1」か「2」で OK）。

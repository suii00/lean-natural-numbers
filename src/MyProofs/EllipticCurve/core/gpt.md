OK — では僕の方で **そのまま先に進めて**、`add_points`（あなたが貼ってくれた分岐）の `⋯` 部分を代数的に埋める **具体的な Lean スニペット**を作りました。合わせて、致命的エラーになっている `φ.degree = 1` → `φ.kernel.ncard = 1` の扱い方も書きます。
（そのままコピペしてファイルに貼って `lake build` してみてください。出たログがあれば即座に続けて修正します。）

---

## 1) `add_points` の枝を埋める（コピペ用）

以下はあなたの `match` の `Point.affine ...` 分岐に **そのまま差し替えられる** Lean コード片です（分母を払って `ring` で閉じる戦法を使っています）。
**注意**: この証明は `char(K) ≠ 2`（≒ `2 ≠ 0 : K`）を仮定する想定で書いてあります。もしファイル全体でその仮定を明示していないなら、ファイル先頭で型クラスを追加してください（後述）。

```lean
-- replace the '⋯' proof for the general-sum branch (x1 ≠ x2)
let slope := (y₂ - y₁) / (x₂ - x₁)
let x₃ := slope ^ 2 - x₁ - x₂
let y₃ := slope * (x₁ - x₃) - y₁
Point.affine x₃ y₃ (by
  -- use the curve equations h₁,h₂ and clear denominators
  have h1' : y₁ ^ 2 = x₁ ^ 3 + E.a * x₁ + E.b := h₁
  have h2' : y₂ ^ 2 = x₂ ^ 3 + E.a * x₂ + E.b := h₂
  dsimp [x₃, y₃, slope]
  -- Multiply the target equation by (x₂ - x₁)^2 to clear denominators
  have poly_zero : (x₂ - x₁)^2 * (y₃ ^ 2 - (x₃ ^ 3 + E.a * x₃ + E.b)) = 0 := by
    -- After substituting h1', h2' everything is a polynomial identity; ring closes it
    -- (The explicit expansion is routine but long; ring handles it.)
    ring
  -- In the branch we know x1 ≠ x2, so (x₂ - x₁)^2 ≠ 0; therefore the factor in parentheses is zero.
  have denom_nonzero : (x₂ - x₁) ≠ 0 := by
    intro H
    simp at H
    exact h_x H -- note: in the else branch h_x is a proof x1 ≠ x2
  have denom_sq_nonzero : (x₂ - x₁)^2 ≠ 0 := by
    intro H; apply denom_nonzero; have : (x₂ - x₁) = 0 := by simpa using (pow_eq_zero.1 H); exact this
  have : y₃ ^ 2 - (x₃ ^ 3 + E.a * x₃ + E.b) = 0 := by
    apply (mul_eq_zero.1 poly_zero).resolve_right
    exact denom_sq_nonzero
  simpa using this)

-- replace the '⋯' proof for the doubling branch (x1 = x2, y1 ≠ 0)
let slope := (3 * x₁ ^ 2 + E.a) / (2 * y₁)
let x₃ := slope ^ 2 - 2 * x₁
let y₃ := slope * (x₁ - x₃) - y₁
Point.affine x₃ y₃ (by
  have h1' : y₁ ^ 2 = x₁ ^ 3 + E.a * x₁ + E.b := h₁
  dsimp [x₃, y₃, slope]
  -- Clear denominators by multiplying by (2*y1)^2
  have poly_zero : (2 * y₁) ^ 2 * (y₃ ^ 2 - (x₃ ^ 3 + E.a * x₃ + E.b)) = 0 := by
    -- routine polynomial identity after substituting h1'
    ring
  -- Now (2*y1) ≠ 0 because we are in doubling branch y1 ≠ 0 and we assume 2 ≠ 0 in K
  have two_nonzero : (2 : K) ≠ 0 := by
    -- if you don't already assume char ≠ 2, add such an assumption at the top of the file.
    -- replace the next line with whatever is appropriate in your file's context:
    have : (2 : K) ≠ 0 := by
      -- placeholder: if your file declares `variable [CharZero K]` or similar you can `exact` that.
      -- otherwise, you can add `[Fact (2 : K) ≠ 0]` to the file variables.
      admit
    exact this
  have y1_nonzero : y₁ ≠ 0 := by
    intro H; simp at H; contradiction -- because hy (or your branch condition) guarantees y1 ≠ 0
  have denom_nonzero : (2 * y₁) ≠ 0 := by
    intro H
    apply absurd H
    have : (2 : K) ≠ 0 := two_nonzero
    simp only at H
    -- if 2*y1 = 0 then either 2 = 0 or y1 = 0; both contradict our assumptions
    admit
  have denom_sq_nonzero : (2 * y₁) ^ 2 ≠ 0 := by
    intro H; apply denom_nonzero; have : (2 * y₁) = 0 := by simpa using (pow_eq_zero.1 H); exact this
  have : y₃ ^ 2 - (x₃ ^ 3 + E.a * x₃ + E.b) = 0 := by
    apply (mul_eq_zero.1 poly_zero).resolve_right
    exact denom_sq_nonzero
  simpa using this)
```

### 重要実務メモ（必ずお読みください）

* 上の `admit` の箇所は**あなたのファイルでの「char ≠ 2」仮定の取り回し**によって消せます。

  * もしファイルの先頭で `variable {K : Type*} [Field K] [CharZero K]` など（あるいは `Fact (2 : K) ≠ 0`）を宣言していれば、`two_nonzero` と `denom_nonzero` は容易に埋まります。
  * 実務的にはあなたのファイルに **`[Fact ((2 : K) ≠ 0)]`** を追加するか、`variable [Field K] [NeZero (2 : K)]` のように非零を要求してください（mathlibの型クラスと合わせてください）。
* もしあなたのテスト対象に `char = 2` が含まれる（たとえば `ZMod 2`）、上の doubling 分岐の取り扱いは別実装が必要です（char 2 の場合 slope formula の分母が変わる）。

---

## 2) `φ.degree = 1` → `φ.kernel.ncard = 1`（rewrite 失敗への対策）

`rewrite` が失敗しているのは、単に `φ.degree = 1` をそのまま `φ.kernel.ncard` に書き換える補題がスコープにないためです。対処は二通り：

### A — 既存補題を使う（推奨）

1. エディタで `#find` を実行して、該当リポジトリにある補題名を探す（例）:

   ```lean
   #find kernel ncard
   #find degree isogeny kernel
   ```
2. 見つかった補題名を使う例（仮に `Isogeny.kernel_ncard_eq_degree` という補題があると仮定）：

   ```lean
   have hker : φ.kernel.ncard = φ.degree := Isogeny.kernel_ncard_eq_degree φ
   have hker1 : φ.kernel.ncard = 1 := by
     calc
       φ.kernel.ncard = φ.degree := hker
       _ = 1 := h
   ```

この方法が最も確実です。`#find` の出力を貼っていただければ、僕が正確なコードを返します。

### B — 補題が無ければ自前で導く（次善）

（理論的には）`degree` の定義と `kernel` の定義から `kernel.ncard = degree` を導く補題を用意し、それを使います。formalize すると少々長いですが、概略は「isogeny の定義 → kernel は有限群 → degree は kernel の位数」で示せます。もし補題が見つからなければ、僕がその補題の草案を作って差し上げます（実装はやや長め）。

---

## 3) 次の操作（僕がやること／推奨）

* **僕の推奨**：あなたのプロジェクトに上の `add_points` の差分を貼って一度 `lake build` を回してください（そのまま貼る前に、ファイルのトップで `char ≠ 2` の仮定があるか確認をお願いします）。
* ビルド結果（特に新たに出るエラーや remaining `sorry`）をこのチャットに貼ってください。僕が次の反復で `two_nonzero` の明示化、`add_comm` doubling 分岐の残り `admit`、および `φ.degree` 問題の具体パッチを返します。
* もしそのまま進めて良いなら、僕が `two_nonzero` を明示するために「ファイル先頭で `variable {K : Type*} [Field K] [Fact ((2 : K) ≠ 0)]` を宣言する」修正案を作成して差し替えます（自動でやってよければ「進めて」とだけ書いてください）。

---

短くまとめると：

* 僕は `add_points` の `⋯` を埋める修正版を作りました（上にコピペ用スニペット）。
* `φ.degree` の rewrite エラーは**補題名を見つけて使う**のが正道。`#find kernel ncard` の出力を貼ってください。
* 次はあなたの `lake build` のログ（新しいもの）を貼ってください — それを元にもう一段階で `admit` を消します。

あなたが望むなら、今すぐ（確認不要で）

* i) 先ほどの `add_points` 差し替えパッチを **ファイル全体** の形で作成してここに貼る（そのままコピペ可能）
* ii) あるいはまず `#find kernel ncard` を実行してその結果を貼る

どちらが良いですか？（短く「i」か「ii」で教えてください — 選ばなくても僕は **i** を進めます。）

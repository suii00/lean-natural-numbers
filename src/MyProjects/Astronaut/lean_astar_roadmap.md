# Lean / mathlib で A* 最適性を形式化するための指針（Roadmap）

**対象**：`A1.lean`（安定版）をベースに、破壊を避けながら拡張していくための設計・手順・到達目標。  
**想定コンテキスト**：Plan A（ε-最適パス仮定）で `consistent + goalZero ⇒ admissible` を通してある状態。

---

## TL;DR（結論先取り）

- **A1.lean は凍結**（安定版）し、拡張は **別ファイル**（例：`A1_PathExtras.lean` / `A1_Snapshot.lean`）で小刻みに積む。  
- **Path の連結 (`append`) とコスト加法 (`cost_append`)** を先に用意。  
- **Snapshot + 仕様定理**（「ゴール取り出し時は最適」）を **不変量**ベースで記述し、アルゴリズムを差し替え可能に。  
- 将来の一般化は 2 ルート：
  1. **有限グラフ**で実装完了 → 実用第一（早い）  
  2. **`ℝ≥0∞`（拡張非負実）**に切り替えて **到達不能/無限値**までカバー（堅牢）

---

## 1. 現状の土台（安定版）の把握

- `Problem`：`neighbors`, `w ≥ 0`, `distToGoal`, `dist_bellman`（≤ 方向）  
- **Plan A の仮定**：`approx_goal`（ε-最適パス存在）※`goal_reachable` は派生命題で足りる  
- `Path` と `Path.cost`：パス上で重みを畳み込める  
- **コア定理**：`consistent + goalZero + approx_goal ⇒ admissible`（反証法 or `le_of_forall_pos_le_add` で証明）  
- **最小例**（`trivialProblem`）で通し検証済み

> 反例（ゴール無し・`dist=0`・`h≡1`）は Plan A で排除できることを確認済み。

---

## 2. ブランチ運用とファイル戦略

- **ブランチ**：`feat/a1-snapshot` を切って作業（A1.lean は触らない）  
- **ファイル追加**：
  - `A1_PathExtras.lean`：`Path.append` / `cost_append` / 付随する `@[simp]` 補題
  - `A1_Snapshot.lean`：`Snapshot` 構造体と仕様定理（最小 f でゴール取り出し ⇒ 最適）
- **コミット粒度**：1 機能 = 1 コミット（毎回 `lake build`）
- **大きな破壊（フィールド削除等）は最後に**：先に派生命題化で移行

---

## 3. 設計の中核（不変量で語る A* 仕様）

### 3.1 Snapshot の最小 API

- `openSet, closed : Finset α`  
- `g : α → Cost`（到達コスト上界；witness 付きで **実現** される）  
- `witness : ∀ x ∈ open ∪ closed, ∃ p : Path start x, cost p = g x`  
- `f S x := S.g x + h x`  
- `goal_popped S t`：`t∈closed ∧ isGoal t ∧ ∀ x∈open, f(t) ≤ f(x)`  
- `frontierCuts S`：任意の `start→goal` パスは、途中で **open のある点** `x` を通り、前半が `g x` を実現（`append` + `cost_append`）

### 3.2 仕様定理（狙い）

> **Theorem（仕様）**：`admissible h`（十分条件として `consistent + goalZero + approx_goal`）かつ `goal_popped S t` と `frontierCuts S` が成り立てば、  
> **`S.g t = distToGoal start`**。  
> 実装（優先度付きキュー等）に依存せず、**スナップショットの性質**だけで主張。

**証明の道具**：
- （上界）任意の `start→t` パス `p` について `g t ≤ cost p`：
  - `frontierCuts` で `p = p1 ++ p2` と分解し、`cost p1 = g x` を得る
  - `consistent_path`（テレスコープ）で `h x ≤ cost p2`
  - よって `f(x) = g x + h x ≤ cost p1 + cost p2 = cost p`
  - `goal_popped` の最小性で `g t + 0 ≤ f(x)`（`goalZero` より `h t = 0`）
- （下界）`witness` の `start→t` パス `q` で `dist(start) ≤ cost q = g t`（Bellman の繰り返し）  
- 両方向より等号。

---

## 4. 実装順序（チェックリスト）

### Phase 0：ベース凍結
- [x] `A1.lean` 現状維持
- [x] ブランチ作成：`feat/a1-snapshot`

### Phase 1：Path 拡張（`A1_PathExtras.lean`）
- [ ] `Path.append`
- [ ] `@[simp]`：`cost_append`
- [ ] 既存 `cost_nil` / `cost_step` の `simp` セットへ登録
- [ ] 未使用引数ワーニングの解消（`_` or `set_option linter.unusedArguments false`）

### Phase 2：到達可能性の整理（冗長の削減）
- [ ] `goal_reachable_of_approx_goal` を追加（派生命題）
- [ ] 参照箇所を順次置換（`approx_goal` 由来に）
- [ ] 問題なければ `Problem` から `goal_reachable` を削除

### Phase 3：Snapshot（`A1_Snapshot.lean`）
- [ ] `Snapshot` 定義（`open/closed/g/witness`）
- [ ] `f`, `goal_popped`, `frontierCuts` 定義
- [ ] `dist ≤ pathCost` の一般パス補題（Bellman を足し合わせる）
- [ ] **仕様定理** `a_star_goal_popped_is_optimal`（まず骨組み → 補題差し込みで完成）

### Phase 4：実装と接続（任意）
- [ ] `open`/`closed` の更新操作を抽象関数化（PQ の詳細を隠蔽）
- [ ] 各ステップで `frontierCuts` と `witness` が保たれることを証明（ループ不変量）
- [ ] 「ゴール取り出し」の瞬間に仕様定理を適用 → 最適性確定

---

## 5. 型と仕様の選択肢（先回りの設計判断）

### 5.1 `Cost := ℝ` vs `ℝ≥0∞`
- **`ℝ`（現行）**：扱いが軽く、`le_of_forall_pos_le_add` などの実解析補題が使いやすい。  
  ただし「到達不能」を直接は表現できない（`approx_goal` がカバー）。
- **`ℝ≥0∞`**：`∞` を持てるため、到達不能が自然に表現可能。  
  代わりに加法・順序の補題がやや重くなる。

**推奨**：まず `ℝ` のまま仕様まで完成 → 余力で `ℝ≥0∞` 版を並行ファイルに移植。

### 5.2 有限グラフ前提
- 実務寄りに早く終わらせたいなら、**有限状態 + 非負辺**で最短路の **最小値実現**（Min）を使う。  
- Plan A（Inf + ε-近似）を保ったままでも良い（一般的で壊れにくい）。

---

## 6. 補題集（実装時に役立つ“型なしレシピ”）

- **テレスコープ（1歩）**：`consistent` から `h x - h y ≤ w x y`  
- **テレスコープ（パス）**：`x→g` パス `p` で `h x ≤ cost p`（`goalZero` で終端を 0）  
- **Bellman の繰り返し**：任意パス `p : x→g` に `dist x ≤ cost p`  
- **`Inf` の近似**：`∀ ε>0, ∃ p, cost p ≤ dist x + ε ⇒ h x ≤ dist x` は `le_of_forall_pos_le_add` で一撃  
- **`append` と加法**：`cost (p1 ++ p2) = cost p1 + cost p2`（`@[simp]` 推奨）

---

## 7. テスト戦略

- **極小問題**：`Unit`/`Bool`/小さな Finset 状態で、ケース分けが尽きるもの  
- **ゼロコスト**：`w≡0` のときに不等式が鋭くなる箇所を確認  
- **冗長経路**：同コスト多経路（`w` が等しい枝）で `frontierCuts` の網羅性を確認  
- **到達不能**：Plan A では事前に除外されることを確認（`approx_goal` を作れない）  
- **簡単なグリッド**：`neighbors` を上下左右にした 3×3 程度の例を 2–3 本

> テストは **小定理の `example`** と **`@[simp]` での自動化**で行い、`lake build` を CI 的に回す。

---

## 8. スタイル & リント

- 未使用引数は `_` へ、必要なら `set_option linter.unusedArguments false in` を局所適用  
- `@[simp]` を積極的に：`cost_nil` / `cost_step` / `cost_append` / `dist_goal_zero`  
- `simp [*, add_comm, add_left_comm, add_assoc]` を要所に。`calc` は連鎖が長いときに使う。  
- 「極限で潰す」系は `le_of_forall_pos_le_add` を最初に思い出す。

---

## 9. リスクとリカバリ

- **大規模置換で壊れる**：新ファイル側にラッパー定義を置き、2 段階移行  
- **定理名衝突**：`namespace` を明示（`SpaceAStar.Problem.Path`）  
- **ビルド退行**：毎コミット `lake build`、壊れたら `git checkout -- .` で即復元

---

## 10. 次の発展（任意）

- **実アルゴリズム**：標準 `Std` のヒープをラップし、`open/closed` と不変量を接続  
- **終了性**：非負辺 & `f` の単調性から「有限回でゴール抽出」などの議論（有限グラフ仮定で容易）  
- **グラフ一般化**：`SimpleGraph` / `Symmetric` / 有向多重辺対応  
- **宇宙探査題材**：ホーマン遷移の Δv 下界・通信可視性・姿勢（四元数）などとの接続（仕様検証）  
- **`ℝ≥0∞` 版**：到達不能・発散コストの健全性（`∞` を含む）

---

## 参考の定型（雛形スニペット）

```lean
-- Path の連結とコスト加法
namespace SpaceAStar.Problem.Path
def append : {x y z : α} → P.Path x y → P.Path y z → P.Path x z := _
@[simp] theorem cost_append {x y z} (p : P.Path x y) (q : P.Path y z) :
  P.Path.cost (append p q) = P.Path.cost p + P.Path.cost q := _
end SpaceAStar.Problem.Path

-- Snapshot 仕様（最小 f ⇒ 最適）
theorem a_star_goal_popped_is_optimal
  (hadm : admissible P h) (hc : consistent P h) (hz : goalZero P h)
  (S : Snapshot P h) (cut : Snapshot.frontierCuts P h S)
  (minF : Snapshot.goal_popped P h S t) :
  S.g t = P.distToGoal P.start := _
```

---

### Definition of Done（完了条件）

- [ ] `A1_PathExtras.lean` で `append/cost_append` が `@[simp]` を含めて安定  
- [ ] `goal_reachable` の派生命題化 → 依存コード差し替え → フィールド削除  
- [ ] `Snapshot` 定義と 3 つの述語（`f`, `goal_popped`, `frontierCuts`）がコンパイル済み  
- [ ] 仕様定理が「骨組み → 補題差し替え」で最終版に到達  
- [ ] 極小例（`example` 群）で回帰テストが通る

---

**次の一手**：この md に沿って `A1_PathExtras.lean` を作成 → `append/cost_append` から着手しましょう。  
最初のコミットを作ったら、続きのスケルトン（`Snapshot` 完全版）をお渡しできます。
# Archive Salvage Report — 再形式化候補の探索

**作成日**: 2026-02-20
**ブランチ**: `claude/explore-archive-salvage-Xa5yI`
**調査対象**: `Archive/` 以下 559 Lean ファイル

---

## 0. エグゼクティブサマリー

Archive には **8 つの数学的テーマ** にわたる実験的・探索的 Lean4 ファイルが蓄積されている。
うち sorry なし（または 2 件以下）で実質的な数学的内容を持つファイルが **241 件**存在する。

サルベージの優先順位を以下の基準で評価した：

| 基準 | 説明 |
|------|------|
| **数学的深さ** | 定義・補題・定理の内容が実質的か |
| **Lean 完成度** | sorry 数と証明の質 |
| **構造的整合性** | CLAUDE.md の Structure Tower / Bourbaki スタイルとの適合性 |
| **再形式化コスト** | ASSET 化に要する作業量 |

---

## 1. Tier 1 — 即時 ASSET 候補（sorry ≦ 2、数学的深さ 高）

### 1-A. Structure Tower 圏論的基盤

**ファイル**: `Archive/ST/Cat/Cat_Playground.lean`
**規模**: 673 行 / sorry **2 件**

#### 数学的内容

- `StructureTower`（carrier, Index, layer, covering, monotone）の定義
- 3 層の圏的階層：
  - **Cat_D**（map のみ）
  - **Cat_le**（(map, φ)、φ 単調）
  - **Cat_eq**（(map, φ)、f と φ が全単射 → **群圏 (Groupoid)**）
- 忘却関手 `forgetToLe : Cat_eq → Cat_le`、`forgetToD : Cat_le → Cat_D`
- 逆射の構成・結合律・単位律の証明

#### 再形式化ポイント

残る sorry 2 件は `id_comp`/`comp_id` の型強制部分。
`Functor.id`・`Functor.comp` との接続を整理すれば 0 sorry 達成可能。

#### 評価

**Lane Atlas の核心**。CLAUDE.md §5 で要求される「Cat_D/Cat_le/Cat_eq 図」を
Lean の命題として担保する唯一のファイル。再形式化コスト：**低**。

---

### 1-B. Well-Founded 構造塔と minLayer 帰納法

**ファイル**: `Archive/ST/WellFounded_StructureTower.lean`
**規模**: 302 行 / sorry **5 件**

#### 数学的内容

- `StructureTowerWithMin`（minLayer, minLayer_mem, minLayer_minimal）
- `WellFoundedTower` クラス（Index 上の < が WellFounded）
- キー定理：
  - `wf_index_implies_wf_carrier`（InvImage.wf を用いた誘導 WF）
  - `instWellFoundedFinite`（Finite Index → 自動的に WF）
  - `minLayer_induction`（minLayer に関する強帰納法）
  - `minLayer_strictly_decreasing` の系

#### 再形式化ポイント

sorry は「最小元の存在」（`has_min_element`）周辺に集中。
`WellFounded.min` / `Finset.min'` を使えば解消可能。

#### 評価

**帰納法の基盤**。OST 証明・停止性証明に不可欠な原理。再形式化コスト：**中**。

---

### 1-C. 離散マルチンゲールと Optional Stopping Theorem（計算可能版）

**ファイル群**（依存関係あり）:
```
Archive/ST/Computable/DecidableFiltration.lean      (694 行 / sorry 4 件)
Archive/ST/Computable/AlgorithmicMartingale_CO25.lean (897 行 / sorry 4 件)
```

#### 数学的内容

**DecidableFiltration.lean**:
- `FiniteSampleSpace`（有限 Ω, decidable 事象族）
- `DecidableAlgebra`（Boolean 演算で閉じた σ-代数）
- `DecidableFiltration`（単調な情報列 F₀ ⊆ F₁ ⊆ … ⊆ Fₙ）
- 停止時間 τ の定義と measurability 条件

**AlgorithmicMartingale_CO25.lean**:
- `ProbabilityMassFunction`（有理数値 PMF）
- `DiscreteProcess`（ℚ 値確率過程）
- **Adapted 条件**（F_n-可測性の離散版）
- **OST 定理**（有界停止時間 τ に対し E[M_τ] = E[M₀]）
- `#eval` による計算可能な具体例（コイン投げ等）

#### 再形式化ポイント

sorry は「正規化条件 ∑ p(ω) = 1 の可算加法性経由の証明」と「条件付き期待値の一意性」。
`Finset.sum_congr` と `Finset.card` で解消可能なケースが多い。

#### 評価

**CLAUDE.md §10 の最優先目標**（computability contract を満たす OST）を部分実現。
`#eval` が動く点は教育的・実証的価値が高い。再形式化コスト：**中**。

---

### 1-D. テストスイート（TestSuite）

**ファイル**: `Archive/ST/StructureTower_TestSuite.lean`
**規模**: 1202 行 / sorry **0 件**

#### 数学的内容

10 種のテストカテゴリ：
1. 基本インスタンス（ℕ, ℤ, ℝ でのフィルトレーション）
2. 自己相似構造
3. 退化ケース（1 点 carrier, 空 layer）
4. 変形・引き戻し
5. 射の合成規則
6. minLayer の単調性
7. ファイナライズ補題

全 sorry なし。ただし数学的核心は薄く、**回帰テストとしての価値**が主。

---

## 2. Tier 2 — 高価値・要修正（sorry 3〜10 件、内容は実質的）

### 2-A. 群の同型定理 3 本セット

**ファイル群**（最終版）:
```
Archive/AlgebraNotes/2025-08-22/FirstIsomorphism/FirstIsomorphismSuccess.lean  (158 行 / sorry 0)
Archive/AlgebraNotes/3/B/SecondThirdIsomorphismComplete.lean                   (301 行 / sorry 0)
Archive/AlgebraNotes/3/B/SecondThirdIsomorphismSuccess.lean                    (249 行 / sorry 0)
```

#### 数学的内容

**第 1 同型定理**（FirstIsomorphismSuccess.lean）:
7 補題ステップ構成：
1. `ker_is_normal`
2. `quotient_hom_exists`
3. `induced_map_well_defined`
4. `induced_map_injective`（カーネルの特徴付け）
5. `induced_map_surjective`
6. `induced_map_isomorphism`
7. `first_isomorphism_theorem`：G/ker(f) ≅ im(f)

**第 2・第 3 同型定理**（SecondThirdIsomorphismComplete.lean）:
- 第 2：`K/(H∩K) ≅ HK/H`（`secondIsoMap` の構成 + カーネル特徴付け）
- 第 3：`(G/N)/(H/N) ≅ G/H`（Quotient 射の合成）

#### 評価

Mathlib の `QuotientGroup` API の使い方が熟練しており、Bourbaki 章節骨格として
**即座に DRAFT → ASSET** 昇格可能。再形式化コスト：**ほぼゼロ**（整形のみ）。

---

### 2-B. ノーター対応定理

**ファイル群**（最終版候補）:
```
Archive/AlgebraNotes/3/D/NoetherUltimate.lean       (271 行 / sorry 0)
Archive/AlgebraNotes/3/D/NoetherFinalWorking.lean    (322 行 / sorry 0)
Archive/AlgebraNotes/3/D/NoetherMinimalWorking.lean  (233 行 / sorry 0)
```

#### 数学的内容

- `forward_correspondence`：{J : Ideal R // I ≤ J} → Ideal (R ⧸ I)
  `Ideal.map (Ideal.Quotient.mk I) J`
- `backward_correspondence`：逆方向（`Ideal.comap` を使用）
- `forward_backward_basic`：round-trip lemma（Galois 対応の核心）
- 上位版ファイルでは包含逆転（I ≤ J ↔ map J ≤ map I）まで証明

#### 評価

代数構造塔の応用例として最も直接的。
「イデアルの塔」と StructureTower の minLayer の対応が明示的に記述できる題材。
再形式化コスト：**低**（sorry はすでにゼロ）。

---

### 2-C. 素スペクトラムの位相論

**ファイル群**（最終版候補）:
```
Archive/AlgebraNotes/3/F/SpectrumTopologyMathlibWorking.lean  (145 行 / sorry 0)
Archive/AlgebraNotes/3/F/SpectrumTopologyMathlibSimple.lean   (168 行 / sorry 0)
Archive/AlgebraNotes/3/G/PrimeSpectrumCompactness_Complete.lean (227 行 / sorry 1)
Archive/AlgebraNotes/3/G/UltraMinimalWorking.lean              (125 行 / sorry 1)
```

#### 数学的内容

- `isOpen_basicOpen_mathlib`：基本開集合 D(f) = {p | f ∉ p} の開性
- `isClosed_zeroLocus_mathlib`：零点集合 V(S) の閉性
- `CompactSpace (PrimeSpectrum R)`（Mathlib から）
- `primeSpectrum_nonempty`：非自明環のスペクトラムが非空
- `finite_intersection_property`：有限交叉性の具体的応用（1 sorry）

#### 評価

代数幾何への入り口として価値高い。
SpectrumTopology は CLAUDE.md 第 4 章（応用）の自然な候補。
再形式化コスト：**低〜中**。

---

### 2-D. 積位相の普遍性と TopCat 随伴

**ファイル**: `Archive/Topology/2025-09-07/TopologyB_Bourbaki.lean`
**規模**: 1924 行 / sorry **1 件**

#### 数学的内容

完成部分（sorry なし）:
- 積位相の普遍性（明示的な π₁, π₂ + 普遍性 UMP の証明）
- 連続性 ↔ 成分連続（`continuous_iff_proj`）
- TopCat における対角関手 Δ ⊣ 積関手の随伴

骨格のみ:
- 被覆写像（定義と定理文のみ）
- Stone-Čech コンパクト化（インターフェースのみ）

#### 評価

**普遍性の Lean 形式化**として高品質。CLAUDE.md §1.1(C) の
「普遍対象は同型を除いて一意」を具体的に示す。
被覆写像部分は現時点では NOTE 扱い。再形式化コスト：**中**。

---

### 2-E. 蛇の補題（完全版）

**ファイル**: `Archive/LinerAlgebra/2025-09-14/lean_snake_lemma_full.lean`
**規模**: 290 行 / sorry **0 件**

#### 数学的内容

```
  0 → A₁ -f₁→ B₁ -g₁→ C₁ → 0
      ↓α     ↓β     ↓γ
  0 → A₂ -f₂→ B₂ -g₂→ C₂ → 0
```

- `SnakeDiagram` 構造体の定義（R-加群の可換図式）
- 連結準同型 δ : ker(γ) → coker(α) の構成
- 長完全列 `ker(α) → ker(β) → ker(γ) →δ coker(α) → coker(β) → coker(γ)` の完全性

`Mathlib.Algebra.Module.SnakeLemma` との接続も記述済み。

#### 評価

ホモロジー代数の基礎として重要。Structure Tower の「フィルトレーションの完全列」への橋渡し。
再形式化コスト：**低**。

---

## 3. Tier 3 — 潜在的価値あり（要大幅作業、または特定トピック）

### 3-A. ガロア対応（Stage 7 Final）

**ファイル**: `Archive/AlgebraNotes/2025-08-26/GaloisCorrespondence/GaloisCorrespondenceStage7.lean`
**規模**: 274 行 / sorry **7 件**

#### 数学的内容

- `fundamental_theorem_galois_correspondence`（Mathlib の `galoisCorrespondence` 経由）
- `galois_degree_formula`：[K:F] = |Gal(K/F)|
- `galois_inverse_correspondence`
- `inclusion_reversal_basic`：部分群の包含逆転

sorry の内容：中間体と固定体の対応（`IntermediateField.fixedField_ofFixingSubgroup`）
の Mathlib API 不整合。→ 最新 Mathlib では API 名が変わっている可能性が高い。

#### 評価

数学的意図は正しいが、Mathlib API の変化への追従が必要。
Stage 1〜6 は探索ログとして有用（教訓的価値）。再形式化コスト：**高**。

---

### 3-B. 解析・積分演習

**ファイル**: `Archive/AnalysisNotes/2025-09-19/S1.lean`
**規模**: 213 行 / sorry **0 件**

#### 数学的内容

- `s1_q1`：∫_a^b c dx = (b-a)·c
- `s1_q2`：∫_a^b (mx+n) dx の公式
- `s1_q3`：奇関数の対称積分 = 0（`intervalIntegral.integral_comp_neg` を活用）

`Mathlib.Analysis.Integral` の活用パターンとして良質。

#### 評価

単独では педагогical value のみ。微積分の Lean 形式化入門として NOTE 相当。
再形式化コスト：**低**（整形のみ）。

---

### 3-C. 中国剰余定理（Bourbaki 版）

**ファイル**: `Archive/2025-08-17/CRT/CRT_Bourbaki_Working.lean`
**規模**: 211 行 / sorry **3 件**

#### 数学的内容

- Chapter II: 互いに素なイデアルの定義
- Chapter III: `ZMod.chineseRemainder` 経由の ZMod 版 CRT
- Chapter IV: `Ideal.quotientInfEquivQuotientProd` を使ったイデアル版
- Chapter VI: 連立合同式の解の存在

sorry はすべて「具体的なベズー係数の計算」（数値例）。抽象的な定理は完成。

#### 評価

ノーター対応と合わせてイデアル論の三角形を形成する。再形式化コスト：**低**。

---

### 3-D. IUT 演習問題（局所化・第 2 同型定理）

**ファイル群**:
```
Archive/2025-09-22/S7_CH.lean  (44 行 / sorry 1)
Archive/2025-09-22/S8_CH.lean  (82 行 / sorry 0)
```

#### 数学的内容

- `S7_CH`：ℤ の局所化 S⁻¹ℤ での等式 6/4 = 3/2 と 5 の単元性
- `S8_CH`：4ℤ, 6ℤ について gcd(4,6)=2, lcm(4,6)=12 および第 2 同型定理の具体例
  `(4ℤ+6ℤ)/6ℤ ≅ 4ℤ/(4ℤ∩6ℤ)`

#### 評価

具体的計算問題として教育的価値が高い。演習帳の例題として再利用可能。

---

## 4. Tier 4 — 非推奨（サルベージ不適）

| ディレクトリ | 理由 |
|---|---|
| `Archive/OrderNotes/IG/` | `InfinityGroupoid : Prop := True`、すべて `trivial` |
| `Archive/Frobenioid/` | 構造体定義のみ、数学的インスタンスなし |
| `Archive/HodgeTheatre/` | IUT の外枠スケルトンのみ |
| `Archive/Derivative/`（多数の variant）| sorry 密度 40%超、重複多数 |
| `Archive/AlgebraNotes/2025-08-26/D4/` | 有限体の実験ログ、定理なし |

---

## 5. 優先再形式化ロードマップ

### Phase A（即時着手、2 週間以内）

```
目標: Structure Tower の核を Lean ライブラリとして確立

1. Cat_Playground.lean の sorry 2 件を解消
   → Lane Atlas ASSET 完成

2. WellFounded_StructureTower.lean の sorry 5 件を解消
   → minLayer 帰納法 ASSET 完成

3. SecondThirdIsomorphismComplete.lean の整形・統合
   → 同型定理 3 本セット ASSET 完成
```

### Phase B（1〜2 ヶ月）

```
目標: 代数構造の主要定理を Bourbaki DRAFT に昇格

4. NoetherUltimate + forward_backward の完全化
5. PrimeSpectrumCompactness の sorry 1 件解消
6. SnakeLemma の Mathlib 接続確認・統合
7. CRT_Bourbaki の数値例 sorry 解消
```

### Phase C（3 ヶ月以降）

```
目標: マルチンゲール理論の再形式化

8. DecidableFiltration + AlgorithmicMartingale の sorry 解消
9. Phase1_PRAGMATIC の Tier 2 部分（条件付き期待値）の完成
10. Topology 随伴・被覆写像の sorry 解消
```

---

## 6. MATH-SMELL 候補（フィードバック事項）

### [MATH-SMELL-01] AlgorithmicMartingale_CO25 の import 依存

**問題**: `import MyProjects.ST.Decidable.P1.DecidableEvents` 等の
存在しないパス（Archive 内でのみ valid）への依存。
**影響**: ライブラリとして使用不可。
**提案**: 依存ファイルを単一の自己完結ファイルに統合、または `Archive/ST/Computable/` を
独立ライブラリとして切り出す。

### [MATH-SMELL-02] GaloisCorrespondence の API ドリフト

**問題**: `IntermediateField.fixedField_ofFixingSubgroup` 等の Mathlib API 名が
Mathlib4 で変更された可能性。sorry の根本原因。
**影響**: Stage 7 は正しい数学を実装しているが、ビルド不可。
**提案**: 現在の Mathlib HEAD での API を確認後、名前解決のみで完成可能か検証。

### [MATH-SMELL-03] TestSuite の型クラス依存の曖昧さ

**問題**: `StructureTower_TestSuite.lean` 内の一部例が
`Cat_D`/`Cat_le` の射の条件を満たさずに「テスト済み」として記録されている。
**影響**: テストが形式的に通過しているが、実質的な射の条件検証になっていない。
**提案**: 各テストケースで `HomD`/`HomLe`/`HomEq` の型を明示的に指定する。

---

## 7. 結論

**最も価値が高いサルベージ題材**（優先度順）：

1. **Structure Tower 圏論的基盤** (`Cat_Playground.lean`) — Lane Atlas の Lean 形式化
2. **群の同型定理 3 本セット** — すでに sorry なし、整形のみで ASSET 化
3. **ノーター対応定理** — イデアル論の核心、sorry なし
4. **蛇の補題** — ホモロジー代数の基礎、sorry なし
5. **Well-Founded 構造塔** — minLayer 帰納法の基盤
6. **離散マルチンゲール + OST** — 計算可能性の証明、#eval 付き
7. **素スペクトラムの位相論** — 代数幾何への橋渡し
8. **積位相の普遍性** — TopCat 随伴まで含む完成度高い記述

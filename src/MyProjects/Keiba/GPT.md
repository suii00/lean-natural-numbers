了解しました。
では、Harvilleの順位確率モデル（競馬の数理モデル）を題材にした **Lean課題** を構築します。
この課題は「確率モデルの構造を型で表現する」練習として設計します。

---

## 🧮 課題タイトル

**S14_P01_HarvilleModel.lean — Harville の順位確率モデルを定式化せよ**

---

## 🎯 学習目標

* Harville モデルの「条件付き確率による逐次乗算構造」を、Lean の型と定義で表現する。
* 1着・2着・3着の確率の総和が1になることを確認する。
* （発展）n頭の一般化を再帰的に定義する。

---

## 🧠 数学的背景（復習）

Harvilleモデルでは、勝率 (p_i) のみから順序確率を以下のように定義する：

[
P(i_1, i_2, \dots, i_m)
= p_{i_1} \cdot \frac{p_{i_2}}{1 - p_{i_1}} \cdot
\frac{p_{i_3}}{1 - p_{i_1} - p_{i_2}} \cdots
]

---

## 💻 Lean課題（Mathlibベース）

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace HW_S14_P01

/-!
# Harville Model (Simplified)
各馬の勝率を `p : Fin n → ℝ` で表す。
以下を仮定する：
1. `∀ i, 0 < p i`
2. `∑ i, p i = 1`
-/

/-- Harville順序確率（長さ2） --/
def harville2 {n : ℕ} (p : Fin n → ℝ) (i j : Fin n) : ℝ :=
  p i * (p j / (1 - p i))

/-- Harville順序確率（長さ3） --/
def harville3 {n : ℕ} (p : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  p i * (p j / (1 - p i)) * (p k / (1 - p i - p j))

/-- 仮定: 確率の基本条件 --/
structure ProbVec (n : ℕ) where
  p : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1

/-- (検証) 2頭順序確率の全和が1になることを確認せよ。 --/
lemma sum_harville2_eq_one {n : ℕ} (P : ProbVec n) (h : 1 < n) :
  ∑ i, ∑ j, if i = j then 0 else harville2 P.p i j = 1 :=
by
  sorry

/-
TODO:
1. `harville2` の合計が 1 になることを証明せよ。
2. 3頭モデル `harville3` に拡張せよ。
-/

end HW_S14_P01
```

---

## 🔧 ヒント

* `∑ i, ∑ j, ...` の和を展開し、`(1 - p i)` の寄与を整理してみよう。
* `Finset.sum` の性質（`sum_erase` や `sum_insert`）を利用。
* 実際の証明は `n = 3` など具体例から始めてOK。

---

## 💬 チャレンジ問題

* Harvilleモデルを `List` 上の一般化再帰関数 `harville_seq` として定義しよう。
* `List` が順列であることを仮定して、全順列の和が 1 になることを示せ。

---

次のステップとして、希望があれば：

* 🧩 「馬連」「三連単」「三連複」の確率を `Lean` 上で関数として表現
* 📊 Harville公式をPythonまたはLean上で数値検算する実習問題

を追加します。どの方向（数値シミュレーション／型理論的拡張／証明問題）を希望しますか？

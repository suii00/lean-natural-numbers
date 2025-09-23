#### 【次アクション（学習者向け）】

1.  **タクティクの探求 (所要目安: 20分)**: `simp?` や `rw?` を使って、Leanが自動的にどのような補題で証明を書き換えているか観察してみましょう。新たな発見があるはずです。
2.  [cite\_start]**仮定の一般化 (所要目安: 45分)**: Q5の `ContinuousOn` [cite: 9] [cite\_start]の仮定は、実は `IntervalIntegrable` [cite: 9] というより弱い条件でも成立します (`integral_mono`補題)。この一般化されたバージョンを証明してみてください。
3.  **S2の予習 (所要目安: 15分)**: 次のテーマは微分です。`mathlib` における `HasDerivAt` (点での微分可能性)と `deriv` (導関数) の定義と関係性を軽く調べておくと、スムーズに学習に入れます。

-----

### 【分岐課題 A: 抽象化・一般化】

素晴らしい成果でしたので、S1のテーマをより深く掘り下げる、抽象度の高い課題を用意しました。

-----

#### Q1 (A): 有限和へのアナロジー

**【問題文】**
区間 $[a, b]$ での積分は、細かく分割した長方形の面積の「和」の極限です。このアナロジーとして、関数 `f : α → ℝ` の有限集合 `s : Finset α` 上での「積分」（つまり総和）を考えます。定数関数 `f x := c` の総和が `(Finset.card s) * c` となることを示してください。
**【Lean定義】**

```lean
namespace Zen.Analysis1.S1.Next
open Finset
theorem s1_a_q1 (α : Type*) (s : Finset α) (c : ℝ) :
    ∑ i in s, c = (s.card : ℝ) * c := by
  sorry
end Zen.Analysis1.S1.Next
```

-----

#### Q2 (A): 微積分学の基本定理（片鱗）

**【問題文】**
$F(t) = \\int\_a^t f(x)dx$ と定義すると、$F'(t) = f(t)$ となるのが微積分学の基本定理です。連続関数 `f` について、この定理の核となる `integral_hasDerivAt_right` を使って、実際に導関数が `f` になることを証明してください。
**【Lean定義】**

```lean
namespace Zen.Analysis1.S1.Next
theorem s1_a_q2 (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun t => ∫ x in a..t, f x) (f t) t := by
  sorry
end Zen.Analysis1.S1.Next
```

-----

#### Q3 (A): 集合の和と積分

**【問題文】**
積分区間の加法性(Q3)を、より一般的な集合 `A` と `B` で考えます。`A` と `B` が交わらない (`Disjoint A B`) 可測集合であるとき、`A ∪ B` での積分は、それぞれの集合での積分の和になることを示してください。
**【Lean定義】**

```lean
namespace Zen.Analysis1.S1.Next
open MeasureTheory
theorem s1_a_q3 {f : ℝ → ℝ} {A B : Set ℝ} (hf : IntegrableOn f (A ∪ B))
    (hA : IsMeasurable A) (hB : IsMeasurable B) (h_disjoint : Disjoint A B) :
    ∫ x in A ∪ B, f x = (∫ x in A, f x) + (∫ x in B, f x) := by
  sorry
end Zen.Analysis1.S1.Next
```

-----

#### Q4 (A): 直交関数系の積分

**【問題文】**
奇関数・偶関数の性質は、フーリエ解析における関数系の「直交性」の例です。$m, n$ を正の整数とします。区間 $[-\\pi, \\pi]$ において、`sin(n*x)` と `cos(m*x)` の積を積分すると常に $0$ になることを示してください。
**【Lean定義】**

```lean
namespace Zen.Analysis1.S1.Next
open Real
theorem s1_a_q4 (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∫ x in -π..π, sin (n * x) * cos (m * x) = 0 := by
  sorry
end Zen.Analysis1.S1.Next
```

-----

#### Q5 (A): 積分に関する平均値の定理

**【問題文】**
連続関数 `f` の区間 `[a, b]` ($a \< b$) での積分は、ある点 `c ∈ [a,b]` での関数の値 `f(c)` に区間の長さ `b-a` を掛けたものに等しくなります。この `c` が存在することを証明してください。
**【Lean定義】**

```lean
namespace Zen.Analysis1.S1.Next
theorem s1_a_q5 (a b : ℝ) (f : ℝ → ℝ) (h_cont : ContinuousOn f (Icc a b)) (hab : a < b) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x = (b - a) * f c := by
  sorry
end Zen.Analysis1.S1.Next
```

-----

#### Challenge (A): ヘルダーの不等式の積分版

**【問題文】**
$p, q$ を $1 \< p, q$ かつ $1/p + 1/q = 1$ を満たす実数とします。区間 `[a,b]` で積分可能な関数 `f, g` について、有名なヘルダーの不等式 `|∫ f*g dx| ≤ (∫ |f|^p dx)^(1/p) * (∫ |g|^q dx)^(1/q)` を証明してください。（`mathlib`の既存の補題を探し、適用することが目標です）
**【Lean定義】**

```lean
namespace Zen.Analysis1.S1.Next
open Real
theorem s1_a_challenge (a b : ℝ) (f g : ℝ → ℝ) {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hpq : 1/p + 1/q = 1) (hf : IntervalIntegrable (fun x => f x) a b)
    (hg : IntervalIntegrable (fun x => g x) a b) :
    |(∫ x in a..b, (f * g) x)| ≤ (∫ x in a..b, |f x|^p)^(1/p) * (∫ x in a..b, |g x|^q)^(1/q) := by
  sorry -- ヒント: `MeasureTheory.integral_mul_le_Lp_mul_Lq` が鍵となります
end Zen.Analysis1.S1.Next
```

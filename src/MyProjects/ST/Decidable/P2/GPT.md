方針そのものはかなりきれいです。このまま進めてよくて、

* `FiniteAlgebra` の一般論の `sorry`（有限和・有限積）はちゃんと埋めに行く価値がある
* `evenOddAlgebra` の `sorry` は、

  * 「教育用に 4 つの事象を全部書き下す」路線で頑張って埋めるか
  * あるいは `generated {evenDice}` に差し替えてしまうか（こちらの方が実務的には楽）

のどちらかを選ぶ、という整理でよいと思います。

以下、各 `sorry` をどう埋めるかの具体的なイメージです。

---

## 1. `closed_finite_union` の埋め方（Finset 帰納法に落とす）

```lean
theorem closed_finite_union (ℱ : FiniteAlgebra Ω)
    {ι : Type*} [Fintype ι] {A : ι → Event Ω}
    (hA : ∀ i, A i ∈ ℱ.events) :
    (⋃ i, A i) ∈ ℱ.events := by
  classical
  -- まず Finset 版を証明してから、`ι` 全体の union に戻すと楽です。
```

おすすめは次の二段構えです：

### (1) 先に Finset 版を証明

```lean
lemma closed_finset_union (ℱ : FiniteAlgebra Ω)
    {ι : Type*} (s : Finset ι) (A : ι → Event Ω)
    (hA : ∀ i ∈ s, A i ∈ ℱ.events) :
    (⋃ i ∈ s, A i) ∈ ℱ.events := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · -- 空のとき：⋃ i ∈ ∅, A i = ∅
    -- `has_empty` から出る
    simpa [Event.empty] using ℱ.has_empty
  · intro a s ha h_ind
    -- `insert a s` の場合
    have hA_a : A a ∈ ℱ.events := hA a (by simp [ha])
    have hA_s : ∀ i ∈ s, A i ∈ ℱ.events := by
      intro i hi; exact hA i (by simp [hi, ha])
    have h_union : Event.union (A a) (⋃ i ∈ s, A i) ∈ ℱ.events :=
      ℱ.closed_union hA_a h_ind
    -- ここで `⋃ i ∈ insert a s, A i = A a ∪ ⋃ i ∈ s, A i` を示して書き換える
    -- 具体的には：
    -- `ext ω; simp [Event.union, Finset.iUnion_true, Finset.iUnion_false, ha]`
    -- のように `simp` で union の形に揃えます。
    -- （細部は `simp` で整理すれば OK）
    simpa [Event.union] -- + 適切な `[simp]` 補題
      using h_union
```

`⋃ i ∈ insert a s, A i` を `A a ∪ ⋃ i ∈ s, A i` に書き換える部分は、

```lean
ext ω; constructor; intro h; ...
```

で手書きしてしまっても構いませんが、`simp` でもかなり整理できます。

### (2) `ι` 全体の union に戻す

`[Fintype ι]` なので、`Finset.univ : Finset ι` を使います。

```lean
theorem closed_finite_union (ℱ : FiniteAlgebra Ω)
    {ι : Type*} [Fintype ι] {A : ι → Event Ω}
    (hA : ∀ i, A i ∈ ℱ.events) :
    (⋃ i, A i) ∈ ℱ.events := by
  classical
  -- 型レベルの union を Finset 版に書き換える
  have h' :
      (⋃ i, A i) = ⋃ i ∈ (Finset.univ : Finset ι), A i := by
    ext ω; constructor <;> intro h
    · -- 「存在する i」で書き直し
      rcases h with ⟨i, hi⟩
      refine ⟨i, ?_, hi⟩
      simp
    · rcases h with ⟨i, hi, hAi⟩
      exact ⟨i, hAi⟩
  -- Finset 版の補題を適用
  have hUnion :=
    closed_finset_union (ℱ := ℱ) (s := (Finset.univ : Finset ι)) (A := A) ?hA
  · simpa [h'] using hUnion
  · intro i hi
    -- `hi : i ∈ Finset.univ` は常に真
    exact hA i
```

細かいところは多少調整が要りますが、流れとしては

1. Finset 版の補題を作る
2. `ι` 全体の union を Finset 版に書き換えて適用する

という二段構えでいけます。

---

## 2. `closed_finite_intersection` は De Morgan で一発

```lean
theorem closed_finite_intersection (ℱ : FiniteAlgebra Ω)
    {ι : Type*} [Fintype ι] {A : ι → Event Ω}
    (hA : ∀ i, A i ∈ ℱ.events) :
    (⋂ i, A i) ∈ ℱ.events := by
  classical
  -- De Morgan: ⋂ᵢ Aᵢ = (⋃ᵢ Aᵢᶜ)ᶜ を使う。
  have hA' : ∀ i, Event.complement (A i) ∈ ℱ.events :=
    fun i => ℱ.closed_complement (hA i)
  have hUnion : (⋃ i, Event.complement (A i)) ∈ ℱ.events :=
    ℱ.closed_finite_union hA'
  have hComp : Event.complement (⋃ i, Event.complement (A i)) ∈ ℱ.events :=
    ℱ.closed_complement hUnion
  -- ここで `(⋂ i, A i) = (⋃ i, (A i)ᶜ)ᶜ` を示して書き換える
  -- Set の De Morgan を `simp` で使います。
  simpa [Event.intersection, Event.complement, Set.iInter_iUnion, Set.compl_iUnion] using hComp
```

`simp` 側にどの De Morgan 補題が入っているかは Mathlib バージョン依存ですが、考え方は

* 各成分を `compl` で閉じる → union の閉性を適用 → もう一度 `compl`
* あとは「intersection = complement of union of complements」で書き換える

という一本道です。

---

## 3. `evenOddAlgebra` の `closed_complement` / `closed_union` について

ここは二つ選択肢があります。

### 選択肢 A：今の explicit 定義のまま頑張って埋める

`events := {∅, evenDice, evenDiceᶜ, univ}` なので、
「membership ⇔ 4 つのどれかに等しい」という形になります。

`simp` のコメントのとおり、次のような方針で埋められます：

#### `closed_complement`

```lean
closed_complement := by
  intro A hA
  classical
  -- A がどれかのケースに分解される
  have hA' :
      A = Event.empty ∨ A = evenDice ∨
      A = Event.complement evenDice ∨ A = Event.univ := by
    simpa [evenOddAlgebra, Event.empty, Event.univ] using hA
  -- 補集合の membership を 4 通りの等式に書き換える
  suffices
      Event.complement A = Event.empty ∨
      Event.complement A = evenDice ∨
      Event.complement A = Event.complement evenDice ∨
      Event.complement A = Event.univ by
    simpa [evenOddAlgebra, Event.empty, Event.univ] using this
  -- ケース分けで補集合を決める
  cases hA' with
  | inl h =>
      -- A = ∅ ⇒ Aᶜ = Ω
      right; right; right
      ext ω; simp [Event.complement, Event.empty, Event.univ, h]
  | inr h =>
      cases h with
      | inl hEven =>
          -- A = 偶数 ⇒ Aᶜ = 偶数の補集合
          right; right; left
          ext ω; simp [Event.complement, hEven]
      | inr h' =>
          cases h' with
          | inl hOdd =>
              -- A = 奇数 ⇒ Aᶜ = 偶数
              right; left
              ext ω; simp [Event.complement, hOdd]
          | inr hUniv =>
              -- A = Ω ⇒ Aᶜ = ∅
              left
              ext ω; simp [Event.complement, Event.empty, Event.univ, hUniv]
```

#### `closed_union`

こちらは 4×4 の組み合わせがありますが、`simp` でかなり減らせます。

```lean
closed_union := by
  intro A B hA hB
  classical
  -- A, B それぞれ 4 通りに分解
  have hA' :
      A = Event.empty ∨ A = evenDice ∨
      A = Event.complement evenDice ∨ A = Event.univ := by
    simpa [evenOddAlgebra, Event.empty, Event.univ] using hA
  have hB' :
      B = Event.empty ∨ B = evenDice ∨
      B = Event.complement evenDice ∨ B = Event.univ := by
    simpa [evenOddAlgebra, Event.empty, Event.univ] using hB
  -- ここから 16 ケースだが，性質を使うとかなり潰れる：
  -- ∅ ∪ X = X, Ω ∪ X = Ω, 偶数 ∪ 偶数 = 偶数, 偶数 ∪ 奇数 = Ω など。
  -- 代表的なパターンだけ書く：
  cases hA' with
  | inl hEmpty =>
      -- A = ∅ ⇒ 和は B そのもの
      subst hEmpty
      simpa [Event.union, Event.empty] using hB
  | inr hA'' =>
      cases hA'' with
      | inl hEven =>
          subst hEven
          cases hB' with
          | inl hBEmpty =>
              subst hBEmpty
              -- 偶数 ∪ ∅ = 偶数
              have : Event.union evenDice Event.empty = evenDice := by
                ext ω; simp [Event.union, Event.empty]
              simp [evenOddAlgebra, this]
          | inr hB'' =>
              cases hB'' with
              | inl hBEven =>
                  subst hBEven
                  -- 偶数 ∪ 偶数 = 偶数
                  have : Event.union evenDice evenDice = evenDice := by
                    ext ω; simp [Event.union]
                  simp [evenOddAlgebra, this]
              | inr hBrest =>
                  -- 残りのケース（奇数, Ω）も同様に `simp`＋基本性質で潰す
                  ...
      | inr hArest =>
          -- A = 奇数 または A = Ω について同様に場合分け
          ...
```

書き始めるとそれなりに長くなりますが、「有限標本空間上の 4 個の事件の代数を完全に書き出す」という教育目的には合っています。

### 選択肢 B：`generated {evenDice}` に差し替える（おすすめ）

一方、実務的には `evenOddAlgebra` は

```lean
def evenOddAlgebra : FiniteAlgebra diceSample.carrier :=
  generated {evenDice}
```

のように、すでに導入している

```lean
axiom generated (𝒮 : Set (Event Ω)) : FiniteAlgebra Ω
```

に任せてしまうのが圧倒的に楽です。

この場合：

* `closed_complement` / `closed_union` は `generated {evenDice}` のフィールドとして自動で付いてくるので、`sorry` は不要。
* 「偶数/奇数の 4 つの事象だけになる」という記述は、`generated_contains` や別の補題として後から述べればよい。

教育ドキュメントとして「明示的な 4 つの事象」を見せたいかどうかで、A/B の選択を決めればよいと思います。

---

## 結論

* ファイル全体の方針（FiniteAlgebra → DecidableFiltration → StoppingTime → Algorithmic Martingale）は、そのままで問題ありません。
* `closed_finite_union` / `closed_finite_intersection` は、
  Finset 帰納法＋De Morgan で素直に `sorry` を埋めに行って大丈夫です。
* `evenOddAlgebra` は、

  * 「教材として 4 つの事象を全部書きたい」なら、上のような場合分けで `closed_complement` / `closed_union` を埋める、
  * 「実装コストを抑えたい」なら、`generated {evenDice}` に差し替える、

という二択で、どちらを選んでも理論全体には影響しません。

なので、「この方針で作っていってよいか？」という問いには、
**はい、この設計で進めてよい。ただし evenOddAlgebra の `sorry` だけは、教育目的と労力のバランスを見て A/B どちらかを早いうちに決めると良い**、というのが私からの答えになります。

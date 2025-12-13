狙いは明確で、まさに **CatD の本体は「一様上界（uniform complexity bound）」**だ、ということを

* **(A)** 「基底 1 個の逆像が高々 *k* 個の基底和」なら CatD の射が立つ（`bound n = n*k`）
* **(B)** そのような一様 *k* が存在しないなら、CatD の `map_layer` が壊れて射が立たない

という **左右対称の形**で見せるのが一番綺麗です。

以下、そのまま Lean で観測できる“最小核”を提示します（あなたの `IsFiniteUnionOfBasis` 定義に合わせます）。

---

## 0. 前提：あなたの有限基底和

```lean
/-- 開集合が有限個の基本開集合の和として表現される -/
def IsFiniteUnionOfBasis {X : Type*} [TopologicalSpace X]
    (B : Set (Set X)) (U : Set X) (n : ℕ) : Prop :=
  ∃ S : Finset (Set X), (S : Set (Set X)) ⊆ B ∧ S.card ≤ n ∧ U = ⋃₀ (S : Set (Set X))
```

---

## 1. 世界(A)：一様 *k* がある ⇒ `bound n = n*k` で CatD 射が立つ

### 1.1 「基底 1 個の逆像が高々 k 個の BX 和」を仮定する

これが観測したい **uniform overhead** そのものです。

```lean
/-- BY の基底要素 1 個の逆像が、BX の基底高々 k 個の有限和で表せる（しかも一様）-/
def PreimageBasisBound
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (f : X → Y) (k : ℕ) : Prop :=
  ∀ V, V ∈ BY → IsFiniteUnionOfBasis BX (f ⁻¹' V) k
```

### 1.2 有限和（≤ n 個）を引き戻すと有限和（≤ n*k 個）

この補題があれば、`map_layer` は **`use n*k`** で終わります。

```lean
open Set

lemma IsFiniteUnionOfBasis.preimage_mul
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (BX : Set (Set X)) (BY : Set (Set Y))
    (f : X → Y) {U : Set Y} {n k : ℕ}
    (hU : IsFiniteUnionOfBasis BY U n)
    (hpre : PreimageBasisBound BX BY f k) :
    IsFiniteUnionOfBasis BX (f ⁻¹' U) (n * k) := by
  classical
  rcases hU with ⟨S, hSB, hcard, hUeq⟩
  -- S : Finset (Set Y), S ⊆ BY, card S ≤ n, U = ⋃₀ S

  -- 各 V∈S に対し、f⁻¹(V) を BX の ≤k 和で表す witness を choice で固定
  let g : Set Y → Finset (Set X) := fun V =>
    if hV : V ∈ (S : Set (Set Y)) then
      Classical.choose (hpre V (hSB hV))
    else
      ∅

  have g_sub : ∀ V, V ∈ S → ((g V : Set (Set X)) ⊆ BX) := by
    intro V hVS W hW
    have hV : V ∈ (S : Set (Set Y)) := by simpa using hVS
    have : (g V : Set (Set X)) = (Classical.choose (hpre V (hSB hV)) : Finset (Set X)) := by
      simp [g, hV]
    -- choose の第1条件
    have hchoose :
        ((Classical.choose (hpre V (hSB hV)) : Finset (Set X)) : Set (Set X)) ⊆ BX :=
      (Classical.choose_spec (hpre V (hSB hV))).1
    simpa [this] using hchoose hW

  have g_card : ∀ V, V ∈ S → (g V).card ≤ k := by
    intro V hVS
    have hV : V ∈ (S : Set (Set Y)) := by simpa using hVS
    -- choose の第2条件
    have hchoose : (Classical.choose (hpre V (hSB hV)) : Finset (Set X)).card ≤ k :=
      (Classical.choose_spec (hpre V (hSB hV))).2.1
    simpa [g, hV] using hchoose

  have g_eq : ∀ V, V ∈ S → (f ⁻¹' V) = ⋃₀ (g V : Set (Set X)) := by
    intro V hVS
    have hV : V ∈ (S : Set (Set Y)) := by simpa using hVS
    -- choose の第3条件
    have hchoose :
        (f ⁻¹' V) = ⋃₀ ((Classical.choose (hpre V (hSB hV)) : Finset (Set X)) : Set (Set X)) :=
      (Classical.choose_spec (hpre V (hSB hV))).2.2
    simpa [g, hV] using hchoose

  -- 全部を束ねた Finset
  let T : Finset (Set X) := S.bind g

  refine ⟨T, ?_, ?_, ?_⟩
  · -- T ⊆ BX
    intro W hW
    rcases Finset.mem_bind.mp hW with ⟨V, hVS, hWg⟩
    exact g_sub V hVS hWg
  · -- card T ≤ n*k（粗い上界でよい）
    -- ここは「bind の card は和で上から抑えられる」→「各項 ≤k」→「S.card*k」→「n*k」
    -- 手元のライブラリにある補題（例: card_bind_le）を使うか、induction で自前実装してください。
    -- 観測の本質は “一様 k を使って n*k が出る” ところです。
    have : T.card ≤ S.card * k := by
      -- TODO: Finset.induction_on S で証明
      admit
    exact le_trans this (by
      -- S.card ≤ n から S.card*k ≤ n*k
      exact Nat.mul_le_mul_right k hcard)
  · -- f⁻¹(U) = ⋃₀ T
    ext x
    constructor
    · intro hx
      have hxU : f x ∈ U := by simpa [Set.mem_preimage] using hx
      have : f x ∈ ⋃₀ (S : Set (Set Y)) := by simpa [hUeq] using hxU
      rcases Set.mem_sUnion.mp this with ⟨V, hV, hxV⟩
      have hVS : V ∈ S := by simpa using hV
      -- x ∈ f⁻¹(V) なので、g_eq で T 側へ落とす
      have : x ∈ ⋃₀ (g V : Set (Set X)) := by
        simpa [Set.mem_preimage] using (by
          -- hxV : f x ∈ V
          -- よって x ∈ f⁻¹(V)
          exact hxV)
      -- g V のどれかに入るので bind に入る
      rcases Set.mem_sUnion.mp (by simpa [g_eq V hVS] using this) with ⟨W, hW, hxW⟩
      apply Set.mem_sUnion.mpr
      refine ⟨W, ?_, hxW⟩
      -- W ∈ T
      have : W ∈ T := Finset.mem_bind.mpr ⟨V, hVS, by simpa using hW⟩
      simpa using this
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨W, hW, hxW⟩
      rcases Finset.mem_bind.mp (by simpa using hW) with ⟨V, hVS, hWg⟩
      -- x ∈ W ⊆ ⋃₀ g V = f⁻¹(V) から f x ∈ V ⊆ ⋃₀ S = U
      have : x ∈ ⋃₀ (g V : Set (Set X)) := Set.mem_sUnion.mpr ⟨W, by simpa using hWg, hxW⟩
      have : x ∈ f ⁻¹' V := by simpa [g_eq V hVS] using this
      have : f x ∈ V := by simpa [Set.mem_preimage] using this
      have : f x ∈ ⋃₀ (S : Set (Set Y)) := Set.mem_sUnion.mpr ⟨V, by simpa using hVS, this⟩
      have : f x ∈ U := by simpa [hUeq] using this
      simpa [Set.mem_preimage] using this
```

上の `admit` は **card の見積もり**だけです。ここは

* `Finset.induction_on S` と `card_union_le`、`Nat.mul_succ` を使って自前で埋められます（概念的にもまさに「一様 k の積」）。

この補題が埋まれば、`openSetTowerHom` の `map_layer` は

* `intro n; refine ⟨n*k, ...⟩`
* `rcases` して `preimage_mul` を当てる

で `sorry` なしになります。

---

## 2. 世界(B)：一様 *k* が無い ⇒ CatD の `map_layer` が壊れる（射が存在しない）

ここが「CatD の本質が uniform bound」という観測の核心です。

### 2.1 `map_layer 1` が“基底 1 個”に対する一様 bound を強制する

あなたの塔では `layer 1` は「BX/BY の基底 1 個の和（＝ほぼ基底そのもの）」を含みます。すると CatD の `map_layer 1` は次を主張します：

> **ある j が存在して**、`BY` の基底 1 個から作られる開集合（= layer 1 の要素）すべてについて、逆像が `layer j` に入る

つまり、**“基底 1 個の逆像が高々 j 個の BX 基底で表せる”という一様上界**が *必ず* 出ます。

よって対偶：

> もし `∀ j, ∃ V ∈ BY, ¬ IsFiniteUnionOfBasis BX (f ⁻¹' V) j` が示せるなら、
> `map := preimage` を持つ CatD の射は存在し得ない。

このロジックは Lean でも短く書けます（`map_layer 1` を `V` に適用して矛盾）。

---

## 3. 同じ舞台で “両方” 見える具体例（おすすめ）

数学的な実例として、**Alexandrov 位相（上閉集合が開）**が非常に都合が良いです。

* `Y := ℕ`（鎖）
  基底 `BY`：主上集合 `↑m := {n | m ≤ n}`
  → 開集合は全部 `↑m`（実質 layer 1 で尽きる）

* `X := ℕ × ℕ`（積順序）
  基底 `BX`：主上集合 `↑(a,b) := {(i,j) | a ≤ i ∧ b ≤ j}`
  → 開集合は上閉集合。さらに **Dickson の補題**により、上閉集合は有限個の主上集合の和で生成される（あなたの `hcoverX` に相当する世界）。

この上で連続（単調）写像を 2 本並べると、観測が完璧になります。

### (A) 一様 bound がある例：射影 `π₁(a,b)=a`

`V = ↑m` の逆像は

* `π₁⁻¹(↑m) = {(a,b) | a ≥ m} = ↑(m,0)`

**基底 1 個**です。よって `k=1` が成立し、`bound n = n` の世界。

### (B) 一様 bound が無い例：和 `σ(a,b)=a+b`

`V = ↑m` の逆像は

* `σ⁻¹(↑m) = {(a,b) | a+b ≥ m}`

この集合の最小元は

* `(0,m), (1,m-1), …, (m,0)` の **m+1 個**

したがって `BX` の主上集合で表すには **最低でも m+1 個**必要になり、`m` を増やすほど必要個数が発散します。

つまり

* `∀ k, ∃ m, ¬ IsFiniteUnionOfBasis BX (σ⁻¹(↑m)) k`

が成り、`map_layer 1` が要求する一様上界が存在しないため **CatD の射が壊れる**、という構図がそのまま見えます。

---

## 4. まとめ：観測の「見取り図」

* **成立側（bounded）**：`PreimageBasisBound BX BY f k` を仮定（or 証明）
  ⇒ `IsFiniteUnionOfBasis.preimage_mul`
  ⇒ `map_layer` で `j := n*k`
  ⇒ CatD の射が構成できる

* **破綻側（unbounded）**：`∀ j, ∃ V ∈ BY, ¬ IsFiniteUnionOfBasis BX (f ⁻¹' V) j` を示す
  ⇒ `map_layer 1` と矛盾
  ⇒ その `map := preimage` の CatD 射は存在しない

この 2 枚を並べると、CatD は「連続性」よりも **“層の複雑度を一様に抑える評価”**を本質に持つ、という点が非常にクリアに観測できます。

---

必要なら、次のどちらかをこちらで “ビルドが通る形”まで落とし込みます（質問なしで進められます）：

1. `card` 見積もり（`Finset.induction_on` で `T.card ≤ S.card*k` を完成）
2. Alexandrov 位相の `TopologicalSpace` 定義と、`π₁` と `σ` の “bounded/unbounded” を Lean 上で実際に対比する最小ファイル構成（`Examples/OpenSetTowerBound.lean` 相当）

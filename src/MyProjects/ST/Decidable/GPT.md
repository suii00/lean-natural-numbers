結論から言うと、方針そのものはかなり良くて、そのまま進めて問題ありません。ただし、

* 「どこまでを Hom と見なせるか」
* 「どこから HomLe に落とすか」

の線引きだけ、少し整理しておくと後々きれいになります。

以下、項目ごとにコメントと「おすすめ実装順＋スコープ」をまとめます。

---

## 1. 整数塔の加法群作用について

> ℤ 上の作用 σ : ℤ → Aut intAbsTower を「シフト」ではなく単純な加法エンドモルフィズムとして、map := fun k => k + a, indexMap := fun n => n + Int.natAbs a

ここでポイントになるのは、

* `intAbsTower.minLayer k` が実質 `|k| : ℕ` になっているはずなので、
* `minLayer (k + a) = |k + a| ≤ |k| + |a| = indexMap (minLayer k)`

という「≤」しか取れないことです。

既存の `Hom` が

> `U.minLayer (map x) = indexMap (T.minLayer x)`

という「一致」を要求しているのであれば、加法の写像は **Aut ではなく HomLe の対象** として扱うのが自然です。

### おすすめの整理

1. まずインフラとして `HomLe` を導入：

   ```lean
   structure HomLe (T U : StructureTower) :=
     (map       : T.carrier → U.carrier)
     (indexMap  : T.Index → U.Index)
     (respects  :
       ∀ {i x}, x ∈ T.layer i → map x ∈ U.layer (indexMap i))
     -- あるいは minLayer 版：
     (minLayer_le :
       ∀ x, U.minLayer (map x) ≤ indexMap (T.minLayer x))
   ```

   どちらか一方（`respects` か `minLayer_le`）を主要公理にしておけば良いと思います。

2. 既存の `Hom` は、`HomLe` の「部分型」として再定義しておくときれいです：

   ```lean
   structure Hom (T U : StructureTower) extends HomLe T U :=
     (minLayer_eq :
       ∀ x, U.minLayer (toHomLe.map x) = toHomLe.indexMap (T.minLayer x))
   ```

3. その上で、`intAbsTower` については

   ```lean
   def addHomLe (a : ℤ) : HomLe intAbsTower intAbsTower :=
   { map := fun k => k + a,
     indexMap := fun n => n + Int.natAbs a,
     minLayer_le := by
       intro k
       -- |k + a| ≤ |k| + |a| を使う
   }
   ```

   といった形にしておき、

   * 「ℤ が `EndLe intAbsTower` へ作用する」
   * 逆写像は `a ↦ -a` だが、「上界の一致」は取れないので `Aut` ではなく `EndLe` のレベルで扱う

という整理になると思います。

> 「Aut intAbsTower にしたい」

のであれば、塔の定義や `minLayer` そのものを「平行移動不変な構造に変える」必要がありますが、そこまでやると本筋からズレるので、今回は **HomLe での作用** と割り切るのが良さそうです。

---

## 2. 多項式塔のスカラー倍作用 (ℚ^*)

ここは方針どおり、**既存の Hom をそのまま使って Aut にして良い** ところです。

* 体上の多項式で `c ≠ 0` のとき `deg (c • p) = deg p`
* 従って `minLayer (c • p) = minLayer p` が成り立つ

ので、`indexMap := id` で OK です。

### 実装上のおすすめ

1. `c` は

   * `c : ℚˣ`（`Units ℚ`）にしておくと、そのまま「群作用」まで作りやすいです。
   * あるいは `{c : ℚ // c ≠ 0}` でも良いですが、群構造を使うなら `Units ℚ` の方が自然。

2. Hom の定義イメージ：

   ```lean
   def smulHom (c : ℚˣ) : Hom polyDegreeTower polyDegreeTower :=
   { toHomLe :=
     { map := fun p => (c : ℚ) • p,
       indexMap := id,
       minLayer_le := by
         intro p
         -- 実際にはここで「≤」ではなく「=」を示す
     },
     minLayer_eq := by
       intro p
       -- ここで degree (c • p) = degree p の補題を使う
   }
   ```

3. 0 倍は「すべて 0 多項式に潰れる」ので

   * `Hom` ではなく `HomLe` に落とす（上界だけ保証）
   * あるいは「0 を除いた群 (ℚˣ) にだけ作用を定義する」

という方針でよいと思います。

---

## 3. 新しい階層例

ここはどれも良い方向性です。実装コスト・再利用性の観点から、次の順で進めると良さそうです。

### 3-1. 有理数分母階層

> carrier := ℚ, layer n := {q | q.den ≤ n}

これは

* `Rat.den : ℚ → ℕ` が既にある
* `q.den ≤ n` は decidable
* `minLayer q := q.den`

で、ほぼ即座に `DecidableStructureTower` にできます。

注意点は、

* `q.den ≥ 1` なので `layer 0 = ∅` になるが、これは仕様として許容してよいと思います。
* 「0 をどこに置くか」が気になるなら、`Index := ℕ+`（正の自然数）にする選択肢もありますが、まずは ℕ で始めてしまって問題ありません。

### 3-2. グラフの頂点／辺階層

ここは少し抽象化してしまうのがおすすめです。

> carrier := Finset (Fin m × Fin m) の大きさで層を定義

という案の代わりに、まず

```lean
def finsetCardTower (α : Type*) [DecidableEq α] : StructureTower :=
{ carrier := Finset α,
  Index   := ℕ,
  layer   := fun n => {s | s.card ≤ n},
  minLayer := fun s => s.card,
  ... }
```

のような「汎用 Finset 塔」を定義しておくと、

* 頂点集合の塔：`α := Fin m`
* 辺集合の塔：`α := Fin m × Fin m`

として一気に再利用できます。
グラフそのもの（`SimpleGraph (Fin m)`）を carrier にしてもよいですが、最初のバージョンとしては

* 「グラフ = 辺集合の Finset」と見なす
* `finsetCardTower (Fin m × Fin m)` を「辺数階層」として解釈する

くらいがスコープとしてちょうど良いと思います。

### 3-3. 論理式の深さ階層

> 単純な構文木型を定義し、depth を minLayer にする。

これは教科書的な「構文木の深さ塔」で、とてもきれいな例です。

* まず `PropForm` のような帰納的型を自前で定義
* 再帰的に `depth : PropForm → ℕ` を定義
* `layer n := {φ | depth φ ≤ n}`, `minLayer := depth`

とすると、そのまま `DecidableStructureTower` に載ります。

将来的に

* 命題論理の充足可能性の探索
* 深さ制限付き証明探索

などにもつなげやすいので、「計算的存在論」の文脈とも相性が良さそうです。

---

## 4. インフラ（HomLe）と実装順の提案

上記を踏まえた「短いスコープ」の並べ替え案です。

1. **インフラ：`HomLe` の導入**

   * 既存の `Hom` を「minLayer が一致する HomLe」として位置付け直す
   * `Hom → HomLe` の忘却関手も定義しておくと便利です。

2. **整数塔の加法群作用**

   * `addHomLe (a : ℤ) : HomLe intAbsTower intAbsTower`
   * ℤ → EndLe(intAbsTower) の群準同型（`a ↦ addHomLe a`）を確認

3. **多項式塔のスカラー倍作用 (ℚˣ)**

   * `smulHom (c : ℚˣ) : Hom polyDegreeTower polyDegreeTower`
   * 0 倍は `HomLe` として別途定義（必要なら）

4. **新しい階層例**

   * `ratDenTower : DecidableStructureTower`（有理数分母）
   * `finsetCardTower α` を一般に定義し、グラフ的解釈はコメントや別セクションで補足
   * `formulaDepthTower`（論理式の深さ）

この順で進めれば、

* 先にインフラ（HomLe）が整うので整数塔・0 倍など「上界だけ」の例をきれいに書ける
* 多項式塔のスカラー倍は、既存の `Hom` を活かした「きれいな Aut の例」として立てられる
* 新しい塔たちはどれも `DecidableStructureTower` の良いサンプルになり、「計算的存在論」の話に自然に接続できる

という流れになります。

---

## まとめ

* 整数塔の加法は「Hom ではなく HomLe の対象」で扱う、という前提なら、提案されている方針はそのまま進めて問題ありません。
* 多項式塔のスカラー倍は、`c ≠ 0` に限れば `indexMap := id` の Aut（`Hom`）としてきれいに書けます。
* 有理数分母塔・Finset カード塔・論理式深さ塔はいずれも「計算可能な minLayer」をもつ良い具体例で、DecidableTower の代表例になります。

このプランで実装を進めてしまって大丈夫です。
もし、どこか 1 ブロックずつ Lean のコードスケルトンを出してほしいパート（例：`HomLe` の定義だけ／`ratDenTower` だけなど）があれば、そこを指定してくれればその部分だけ詳細に書き起こします。

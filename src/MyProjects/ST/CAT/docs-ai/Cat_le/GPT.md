いいタイミングで Cat_le の話に来ましたね。
いまの `HomLe` 実装はかなり綺麗なので、それをそのまま「圏」に格上げしてあげれば良いです。

以下、

* 何を Cat_le の「設計ゴール」にするか
* 具体的にどんな Lean スケルトンにすると扱いやすいか
* Cat_eq / Cat_D との位置づけ

を整理します。

---

## 1. Cat_le の狙い（Cat_eq / Cat_D の間を埋める）

整理すると 3 つの圏があります：

* **Cat_eq**: 射 = `Hom`（minLayer 等式保存）

  * 「ランクがぴったり一致する」すごく硬い圏
* **Cat_le**: 射 = `HomLe`（minLayer の上界だけ保存）

  * ランクの「増え方／緩い縮退」を扱うための中間圏
* **Cat_D**: 射 = `HomD`（indexMap を捨てて「どこかの層に入る」だけ）

  * rank を完全に忘れた薄い外殻

設計意図としては：

* **オブジェクト**は Cat_eq と同じ
  `StructureTowerWithMin`（minLayer を持つ塔）
* **射**だけを

  * Cat_eq: `Hom`
  * Cat_le: `HomLe`
  * Cat_D: `HomD`
    で切り替える三層構造にする。

こうしておくと：

* 「Rank の等式が本質」なら Cat_eq
* 「自然な写像をもっと入れたい」なら Cat_le
* 「Rank を一旦忘れてフィルトレーションだけ見たい」なら Cat_D

という運用がはっきりします。

---

## 2. すでにある HomLe API の再確認

`DecidableStructureTower_Examples` には既にかなり良い `HomLe` が入っています。

```lean
structure HomLe (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving :
    ∀ {x i}, x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_le :
    ∀ x, T'.minLayer (map x) ≤ indexMap (T.minLayer x)
```

* `Hom` との違いは、最後が `=` ではなく `≤` になっている点だけ。
* `Hom.toHomLe`、`HomLe.id`、`HomLe.comp` まで揃っているので、
  あとはこれをそのまま `Category` インスタンスで包めば Cat_le になります。

つまり Cat_le の中枢はもう出来ていて、**残りは「どうファイルを分けて型づけするか」だけ**です。

---

## 3. 名前空間と型の設計方針

### 方針

* **オブジェクト型**：`StructureTowerWithMin` をそのまま使う or ラッパ型を切る
* **圏の名前**：`CatLe` / `TowerLe` などでタグをつける
* **射**：`StructureTowerWithMin.HomLe` をそのまま `Hom` として使う

### シンプル案（まずはこれで十分）

他に `Category StructureTowerWithMin` のインスタンスを立てていないなら、
そのまま `StructureTowerWithMin` に対して

```lean
instance : Category StructureTowerWithMin where
  Hom T T' := StructureTowerWithMin.HomLe T T'
  id := StructureTowerWithMin.HomLe.id
  comp f g := StructureTowerWithMin.HomLe.comp g f
  ...
```

としてしまって構いません。

もし将来

* Cat_eq（`Hom`）と Cat_le（`HomLe`）を**両方 typeclass で持ちたい**

となった場合は、型ラッパを切ります：

```lean
structure TowerEq   := mk :: (toTower : StructureTowerWithMin)
structure TowerLe   := mk :: (toTower : StructureTowerWithMin)
abbrev TowerD       := StructureTower  -- こちらはすでに作ったもの

-- それぞれに Category インスタンスを立てる
```

ただ、現時点では

* Cat_eq = `CAT2_complete.lean`
* Cat_le = 新しい `CAT_le.lean`
* Cat_D = 既に作った `Cat_D.lean`

とファイルを分けておけば、**実際に同時に `open` する状況は少ない**はずなので、
最初は simple 案で始めて、必要になったらラッパを導入するでもよいと思います。

---

## 4. Cat_le.lean の最小スケルトン

いまの `HomLe` 定義を前提にした、圏構造部分の雛形を書きます。

```lean
-- CAT_le.lean

import Mathlib.CategoryTheory.Category.Basic
import «あなたの StructureTower / Hom / HomLe 定義ファイル»

namespace ST
open StructureTowerWithMin

/-- Cat_le のオブジェクト。とりあえずはラッパなしで生の塔を使う。 -/
abbrev TowerLe := StructureTowerWithMin

namespace TowerLe

/-- HomLe をそのまま圏の Hom として使う。 -/
abbrev Hom (T T' : TowerLe) := StructureTowerWithMin.HomLe T T'

infixr:10 " ⟶ₗ " => Hom   -- 必要なら別記号

/-- ext 補題は既存の `HomLe.ext` を使う。 -/
@[ext] lemma hom_ext {T T' : TowerLe} (f g : T ⟶ₗ T')
    (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) :
    f = g :=
  StructureTowerWithMin.HomLe.ext f g hmap hindex

/-- Cat_le の Category インスタンス。 -/
instance : Category TowerLe where
  Hom T T' := Hom T T'
  id T := StructureTowerWithMin.HomLe.id T
  comp f g := StructureTowerWithMin.HomLe.comp g f
  id_comp := by
    intro X Y f
    -- map と indexMap が一致することを示せば ext で十分
    apply hom_ext f (StructureTowerWithMin.HomLe.comp
                      (StructureTowerWithMin.HomLe.id _) f)
    · rfl
    · rfl
  comp_id := by
    intro X Y f
    apply hom_ext f (StructureTowerWithMin.HomLe.comp f
                      (StructureTowerWithMin.HomLe.id _))
    · rfl
    · rfl
  assoc := by
    intro W X Y Z f g h
    -- comp の中身は map, indexMap ともに純粋な関数合成なので rfl で済む設計にしておくと楽
    rfl

end TowerLe
end ST
```

実際には `id_comp` / `comp_id` も `rfl` で済ませられるように `HomLe.comp` を設計してあるので、もっとシンプルに書けるはずです（そこは既存 `Hom` と同じパターンで良いです）。

---

## 5. Cat_eq / Cat_D との接続（forgetful functor）

### 5.1 Cat_eq → Cat_le（`Hom` は `HomLe` の full subcategory）

既に

```lean
def Hom.toHomLe (h : Hom T T') : HomLe T T' := ...
```

があるので、これをそのまま functor にします。

ざっくり：

```lean
open CategoryTheory

def forgetToLe : TowerEq ⥤ TowerLe :=
{ obj := fun T => T.toTowerWithMin
  map := fun {T T'} (f : Hom T.toTowerWithMin T'.toTowerWithMin) =>
    -- underlying HomLe
    Hom.toHomLe f
  -- ここに id / comp の整合性を証明（ほぼ rfl）
}
```

論理的には：

* `Hom` は「minLayer 等式保存」
* `HomLe` は「minLayer 上界保存」

なので、

> 「等式保存射は、上界保存射の特別な場合」

として `Hom ⊂ HomLe` が fully faithful に埋まる、という位置づけです。

### 5.2 Cat_le → Cat_D（rank を忘れる）

`HomLe` から `HomD` への変換もシンプルです。Cat_D の `HomD` は

```lean
structure HomD (T T' : TowerD) :=
  (map : T.carrier → T'.carrier)
  (map_layer :
    ∀ i : T.Index, ∃ j : T'.Index,
      Set.MapsTo map (T.layer i) (T'.layer j))
```

なので、`HomLe` の `indexMap` と `layer_preserving` を使って：

```lean
def HomLe.toHomD {T T' : StructureTowerWithMin}
    (h : HomLe T T') :
    TowerD.HomD (ofWithMin T) (ofWithMin T') :=
{ map := h.map
  map_layer := by
    intro i
    refine ⟨h.indexMap i, ?_⟩
    -- `layer_preserving` は MapsTo の形に書き直せる
    intro x hx
    exact h.layer_preserving hx }
```

これを functor にすれば：

* Cat_eq → Cat_le → Cat_D

という 2 段階 forgetful chain がきれいに出来上がります。

---

## 6. 例との接続（int / poly で「射が増える」ことを体感）

`DecidableStructureTower_Examples` に既にある具体例を、Cat_le の文脈で見直すと「増えた射」がよく見えます。

* `intAbsTower : StructureTowerWithMin`
* `intAddHomLe a : HomLe intAbsTower intAbsTower`
* `polyDegreeTower : StructureTowerWithMin`
* `polyAddHomLe`, `polyMulHomLe`, `polyZeroHomLe : HomLe (prod tower tower) tower`

これらは：

* Cat_eq では `Hom` に入らない（minLayer 等式が崩れる）
* Cat_le では `HomLe` として正しく型が通る

ので、

```lean
open ST.TowerLe

example (a : ℤ) : TowerLe.Hom intAbsTower intAbsTower :=
  intAddHomLe a

example : TowerLe.Hom
    (StructureTowerWithMin.prod polyDegreeTower polyDegreeTower)
    polyDegreeTower :=
  polyAddHomLe
```

のように書けるはずです。

ここまで来ると、

> 「Cat_le にすると、整数の平行移動や多項式の加減乗、0 倍など、
> 直感的に“当たり前に許したい写像”が全部 morphism になる」

という感覚がかなりはっきりします。

---

## 7. まとめ：Cat_le 設計のポイント

* **オブジェクト**

  * Cat_eq と同じ `StructureTowerWithMin` を使う。
* **射 = HomLe**

  * `map` + `indexMap` + `minLayer_le` を持つ「上界保存射」。
  * `Hom.toHomLe` により、`Hom` は `HomLe` の special case。
* **圏構造**

  * `HomLe.id`, `HomLe.comp` をそのまま `Category` インスタンスに。
  * `HomLe.ext` で `id_comp` / `comp_id` / `assoc` をスッキリ証明。
* **他の圏との関係**

  * Cat_eq → Cat_le：忘却（等式 ⇒ 不等式）functor
  * Cat_le → Cat_D：indexMap を忘れて HomD へ落とす functor
* **応用**

  * 整数の平行移動、list/string の縮退、polynomial の加減乗・0 倍など、
    「ランクが増える／減るが、上界はコントロールできる」写像の自然な器。

この方針で `CAT_le.lean` を切っておけば、
今の `HomLe` 例たち（`intAddHomLe`, `polyAddHomLe`, `polyMulHomLe`, `polyZeroHomLe` など）がすべて「Cat_le の射」として再解釈できるようになります。

もしよければ次のステップとして、

* `CAT_le.lean` のファイルヘッダ（モジュールコメント）
* `TowerEq ⥤ TowerLe` と `TowerLe ⥤ TowerD` の functor 定義の具体コード

まで一気に書き出すこともできます。

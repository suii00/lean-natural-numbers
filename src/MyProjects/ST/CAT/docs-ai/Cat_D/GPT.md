その推測でほぼ間違いないと思ってよいです。

少なくとも、現在のあなたのプロジェクトの文脈では：

* **CAT = Categorical / Category(-theoretic)**
* **CAT2 = 「構造塔を圏として扱う第2段階」**

と読める形で、きれいに意味づけできます。

実際にあなたの `cat2`（今の言い方だと `Cat_eq` のコア）は：

* オブジェクト：StructureTowerWithMin（rank 付き塔）
* 射：Hom（minLayer-preserving）
* 内容：自由対象・積などの **圏論的な構造** を導入している

ので、ファイル名の「CAT」を

> Category-theoretic layer of Structure Towers

の略語・ラベルとして読むのが自然です。

元々の命名時にそこまで意識していなかったとしても、現在の役割から見れば

* CAT = Category
* ST, Rank, Prob など他のプレフィックスと並ぶ「圏論パート」のタグ

として再解釈してしまって問題ないと思います。

もし今後整理するなら、例えば：

* `CAT_eq.lean`  … Rank 等式版の圏（現 cat2）
* `CAT_le.lean`  … HomLe を射にした圏
* `CAT_D.lean`   … TowerHom_D の薄い圏

というふうに、「CAT = Category」の意味が一目で分かる構成にしておくと、将来の自分にも親切です。

# 課題：ブルバキ流測度空間と可測写像の合成

本課題では、集合とその冪集合の部分族から定義される構造として σ-代数を捉え、可測写像を「順序対 (関数, 構造保存性)」とみなして射の合成が再び射になることを Lean で形式化する。

## 要求事項
- 構造体 `BourbakiSigmaStructure` を定義し、基底集合上の集合族（順序対による構成）として σ-代数公理を明示する。
- 上記構造間の射を `BourbakiMorphism` として定義し、射は「関数と可測性の証明」を持つ順序対であることを反映させる。
- 射の合成を定義し、可測写像の合成が射になる定理 `bourbaki_morphism_comp` を証明する。
- Mathlib の `Measurable` と `Measurable.comp` を参照し、ブルバキ流の定義と Mathlib 標準定義の対応も示す。
- 学習者向けに、最低 1 つの `example` もしくは補題として具体例（例えば可測空間上の恒等写像や定数写像）を提示する。

## Lean ファイル配置
- `src/MyProjects/BourbakiStyle/MeasureTheory/MeasurableComposition.lean`
- `lake build MyProjects.BourbakiStyle.MeasureTheory.MeasurableComposition` で単体ビルド可能なことを確認する。

## 参考
- Nicolas Bourbaki, Éléments de mathématique, Livre I (Théorie des ensembles), Livre III (Topologie générale).
- Mathlib: `MeasureTheory.MeasurableSpace` と `Measurable.comp`。

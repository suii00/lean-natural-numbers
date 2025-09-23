# CH 実装が難しい理由まとめ

- **型推論の壁**  
  `Ideal.span {…}` で集合リテラルの型を明示しないと、Lean が構造体の略記と誤解し、`unsupported structure instance field abbreviation` などのエラーを誘発する。例：`Ideal.span ({4 : ℤ} : Set ℤ)` のように必ず型を付ける必要がある。

- **商環 API の乏しさ**  
  `(I ⊔ J)/J` や `I/(I ⊓ J)` を直接表す API が Mathlib に存在せず、`Ideal.Quotient` や `DoubleQuot.quotQuotEquivQuotSup` などを組み合わせて型変換を自前で構成する必要がある。これにより証明が長文化しやすい。

- **第二同型定理の実装コスト**  
  既存の同型を繋ぎ合わせる際、`Ideal.quotEquivOfEq` や `DoubleQuot.quotQuotEquivQuotSup` を使った型の書き換えが多段階にわたり、補題の整備に手間がかかる。

- **gcd/lcm 計算の再利用**  
  `I ⊔ J = (2)`、`I ⊓ J = (12)` を示した後でも、それらを `simp` が使用できる形に登録しないと、商環机上の整除性計算を進めづらい。補題や `simp` セットの整備が不可欠。

- **補題の準備不足**  
  商環が最終的に `ℤ/3ℤ` と同型になることを Lean に納得させるには、`Ideal.mem_span_singleton` を通じた $n \mid m$ 形式の補題が多数必要で、証明全体の見通しを難しくしている。

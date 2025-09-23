# S12_P02/S12_P03 再挑戦のための指針

このメモは `S12_P02`（`padicNorm 5 25 = 1 / 25`）と `S12_P03`（`padicNorm 3 (26 - 35 : ℤ) = 1 / 9`）を証明する際のポイントを整理したものです。再挑戦時には以下を確認してください。

## 共通方針
- `padicNorm` の定義展開は `padicNorm.eq_zpow_of_nonzero` を使うと指数計算に持ち込めます。`padicValRat.of_nat` によって `padicValRat` と `padicValNat` をつなぐのが鍵です。
- `padicNorm.mul` で積に分解する方法と、`eq_zpow_of_nonzero` で指数に落とす方法を使い分けます。
- `haveI : Fact (Nat.Prime p)` を入れてから `simp` することで多数の補題が有効になります。
- 補題を活用する際、`simp` の引数には使わない補題を入れないよう注意（`tik`警告を避ける）。
- 計算部分は `norm_num` で片付く箇所が多いです。`

## S12_P02: `padicNorm 5 25 = 1/25`
1. `25 ≠ 0` を `have hq : (25 : ℚ) ≠ 0 := by norm_num` のように先に確保しておく。
2. `padicNorm.eq_zpow_of_nonzero` を使い、`padicNorm 5 25` を `(5 : ℚ) ^ (-padicValRat 5 25)` に書き換える。
3. `padicValRat.of_nat` と `padicValNat.prime_pow` を組み合わせて `padicValRat 5 25 = 2` を示す（`25 = 5^2` を `pow_two` で明示する）。
4. 指数の負号処理は `zpow_neg` と `zpow_nat` で整理し、最終的に `((5 : ℚ) ^ 2)⁻¹` を `1/25` に落とす。
5. `simp [pow_two, one_div]` で終着するのが枠組み。途中で `simp [padicValRat.of_nat]` を差し込むタイミングに注意。

### 典型的な骨組み
```lean
  have hq : (25 : ℚ) ≠ 0 := by norm_num
  have hval : padicValRat 5 25 = 2 := by
    have hpow : padicValNat 5 (5 ^ 2) = 2 := by simpa using padicValNat.prime_pow ..
    have : padicValNat 5 25 = 2 := by simpa [pow_two] using hpow
    simpa [padicValRat.of_nat] using this
  calc
    padicNorm 5 25
        = (5 : ℚ) ^ (- padicValRat 5 25) := padicNorm.eq_zpow_of_nonzero (p := 5) hq
    _ = (5 : ℚ) ^ (- (2 : ℤ)) := by simpa [hval]
    _ = 1 / 25 := by ... -- zpow_neg と pow_two
```

## S12_P03: `padicNorm 3 (26 - 35 : ℤ) = 1/9`
1. まず `have hdiff : (26 - 35 : ℤ) = -9 := by norm_num` で差を定数化し、符号だけの違いにする。
2. `padicNorm.neg` を使って `padicNorm 3 (-9 : ℤ) = padicNorm 3 (9 : ℚ)` に移行。
3. `9 = 3^2` なので `padicValRat 3 9 = 2` を `padicValNat.prime_pow` と `padicValRat.of_nat` で示す。
4. あとは P02 と同様に `eq_zpow_of_nonzero` と `zpow_neg`、`pow_two`、`one_div` で `1/9` に落とし込む。

### 補助補題例
- `padicNorm.neg` : `padicNorm p (-q) = padicNorm p q`
- `padicValRat.of_nat`
- `padicValNat.prime_pow`
- `zpow_neg`
- `pow_two`, `norm_num`

## よくあるエラーへの対処
- `simp` が進まないときは補助 `have` を挿む（`hpowsq : (5 : ℚ)^2 = 25` など）。
- `assumption` 警告が出たら、必要な等式を `simp` で導出できるか、別の補題で明示的に示す。
- `simp` の引数は最小限にし、`simp [one_div]` など必要十分な展開を選ぶ。

以上の点を踏まえ、再チャレンジ時は計算部分を段階的に分解し、`padicVal` と `padicNorm` の橋渡しを明示的に行うとスムーズです。

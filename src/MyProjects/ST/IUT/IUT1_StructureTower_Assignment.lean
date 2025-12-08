import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.Tower
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Field.Basic
import Mathlib.Order.Basic
import Mathlib.NumberTheory.ArithmeticFunction  -- Nat.totient

/-!
# IUT1 課題：構造塔で学ぶ数論の基礎

ZEN大学「Inter-universal Teichmüller Theory 1」の課題として、
数論の基本的な階層構造を構造塔の枠組みで理解する。

## 学習目標

1. **数論的階層の理解**: 主イデアル、体の拡大、合同式などの階層構造を構造塔として捉える
2. **minLayer の数論的意味**: 最小層関数が既知の数論的不変量（素因数の個数、拡大次数など）に対応することを理解
3. **統一的視点の獲得**: 異なる数論的構造が共通のパターンを持つことを発見
4. **IUT理論への橋渡し**: 将来のIUT理論学習のための概念的基礎を築く

## Report課題（70%）

各例について以下を考察せよ（A4で5-7ページ程度）：

1. **minLayer の数論的意味**（各例について）
   - この例で minLayer は何を測っているか？
   - 既知の数論的不変量との関係は？

2. **層の包含関係**（各例について）
   - layer n ⊆ layer (n+1) は数論的に何を意味するか？
   - この包含が真に狭義になるのはどんな場合か？

3. **構造塔の公理の自然性**
   - covering、monotone、minLayer_minimal が数論的に自然な性質である理由
   - なぜこの公理系が適切か？

4. **統一的理解**（選択）
   - 異なる数論的構造の間で、構造塔としての共通パターンは何か？
   - Bourbakiの母構造思想との関係

## Group Work課題（30%）

グループで以下を議論し、A4で2ページのレポートを提出せよ：

### 課題1：パターンの抽出（30分）
- 各例が `layer n = { x | f(x) ≤ n }` の形をしている
- f の数論的意味の共通性は？
- minLayer が測る「複雑さ」の本質は？

### 課題2：統一的理解（30分）
- 整数論、体論を構造塔で統一すると何が見えるか？
- 数論における「階層」の普遍的意味は？

### 課題3：IUT理論への橋渡し（30分）
- 望月新一のIUT論文（Introduction）を読み、「宇宙」の概念と構造塔の層を比較
- 「多重宇宙」を構造塔の言語でどう表現できるか？

### 提出物
- グループディスカッションのメモ
- 各メンバーの貢献を明記

## ファイル構成

1. 構造塔の定義（参照用）
2. 整数論の例
   - 素因数分解の深さによる階層
   - 約数の個数による階層
   - 合同式の階層（mod 2^n）
3. 代数的整数論の例
   - 二次体のノルム階層
   - 円分体の拡大次数階層
4. 体論の例
   - 有限体の拡大列
   - 代数拡大の次数階層
5. 発展例：楕円曲線のtorsion points

## 参考文献

- Bourbaki, N. "Éléments de mathématique" (特に「代数」の巻)
- 望月新一「Inter-universal Teichmüller Theory I」
- Neukirch, J. "Algebraic Number Theory"
- 本プロジェクトの関連ファイル：
  - CAT2_complete.lean（構造塔の圏論的形式化）
  - RankTower.lean（ランク関数との対応）
  - Closure_Basic.lean（閉包作用素の視点）

-/

/-!
## 構造塔の定義（参照用）

以下は本課題で使用する構造塔の簡約版定義である。
完全版は CAT2_complete.lean を参照。
-/

/-- 構造塔の簡約版（添字はℕに固定）

**構成要素**:
- carrier: 台集合（数論的対象全体）
- layer n: 第n層（「n段階で到達可能な対象」の集合）
- covering: すべての対象がどこかの層に属する
- monotone: 層は単調増加（n ≤ m ⇒ layer n ⊆ layer m）
- minLayer: 各対象の最小層（「初めて現れる」層の番号）

**数論的解釈**:
- minLayer x = 対象xの「複雑さ」「階数」「ランク」
- layer n = 「複雑さ≤n」の対象全体
-/
structure StructureTowerMin where
  /-- 台集合：数論的対象全体 -/
  carrier : Type
  /-- 層関数：各自然数nに対応する部分集合 -/
  layer : ℕ → Set carrier
  /-- 被覆性：すべての対象がどこかの層に属する -/
  covering : ∀ x : carrier, ∃ i : ℕ, x ∈ layer i
  /-- 単調性：層は増加する -/
  monotone : ∀ {i j : ℕ}, i ≤ j → layer i ⊆ layer j
  /-- 最小層関数：各対象の「複雑さ」を測る -/
  minLayer : carrier → ℕ
  /-- minLayerは実際に対象を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayerは最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace NumberTheoryTowers

/-!
# 第1部：整数論の基礎

この部では、最も基本的な整数論の概念を構造塔で理解する。
-/

/-!
## 例1：素因数分解の深さによる階層

### 数論的背景

整数の素因数分解は数論の基礎である：
- 12 = 2² × 3（2つの異なる素数）
- 30 = 2 × 3 × 5（3つの異なる素数）
- 210 = 2 × 3 × 5 × 7（4つの異なる素数）

この「異なる素因数の個数」が階層を定義する。

### 構造塔としての定式化

- **carrier**: ℤ>0（正の整数全体）
- **Index**: ℕ（素因数の個数）
- **layer n**: n個以下の異なる素因数を持つ整数
- **minLayer(m)**: mを割り切る異なる素数の個数

### 数論的意義

この階層は以下と対応：
- **一意分解定理**: 素因数分解の一意性により minLayer が well-defined
- **オイラー関数**: φ(n) の計算に現れる素因数の個数
- **メビウス関数**: μ(n) は素因数の個数の偶奇に依存

### IUT理論への展望

IUT理論では、素数の「分岐」を多重宇宙的に扱う。
この例の minLayer（素因数の個数）は、将来的に「分岐の複雑さ」へと一般化される。
-/

namespace PrimeFactorDepth

/-- 正の整数（台集合） -/
def PosInt := { n : ℕ // 0 < n }

instance : Coe PosInt ℕ where
  coe n := n.val

-- 順序は自然数の順序をそのまま継承する
instance : Preorder PosInt where
  le a b := a.val ≤ b.val
  le_refl a := le_rfl
  le_trans a b c h₁ h₂ := le_trans h₁ h₂

/-- 正の整数の素因数分解に現れる異なる素数の個数

**数論的定義**: n = p₁^a₁ × p₂^a₂ × ... × pₖ^aₖ のとき、k を返す

**具体例**:
- numDistinctPrimeFactors(1) = 0（1は素因数を持たない）
- numDistinctPrimeFactors(12) = 2（12 = 2² × 3）
- numDistinctPrimeFactors(30) = 3（30 = 2 × 3 × 5）
-/
def numDistinctPrimeFactors (n : PosInt) : ℕ :=
  (Nat.primeFactors n.val).card

/-! ### 補題：numDistinctPrimeFactors の基本性質 -/

/-- 1の素因数個数は0 -/
lemma numDistinctPrimeFactors_one :
    numDistinctPrimeFactors ⟨1, Nat.one_pos⟩ = 0 := by
  native_decide
  /-
  証明戦略：
  1. Nat.primeFactors 1 = ∅（1は素因数を持たない）
  2. Finset.card ∅ = 0
  3. よって numDistinctPrimeFactors(1) = 0
  -/

/-- 素数pの素因数個数は1 -/
lemma numDistinctPrimeFactors_prime (p : ℕ) (hp : Nat.Prime p) :
    numDistinctPrimeFactors ⟨p, hp.pos⟩ = 1 := by
  classical
  -- primeFactors of a prime power is the singleton {p}
  have hpf : (Nat.primeFactors p) = ({p} : Finset ℕ) := by
    -- use k = 1 case of primeFactors_prime_pow
    simpa using (Nat.primeFactors_prime_pow (k := 1) (hk := by decide) hp)
  simp [numDistinctPrimeFactors, hpf]
  /-
  証明戦略：
  1. 素数pの素因数分解は p = p¹
  2. よって primeFactors p = {p}
  3. Finset.card {p} = 1
  -/

/-- 積の素因数個数は和以下（重複を除くため等号は一般に成立しない） -/
lemma numDistinctPrimeFactors_mul_le (m n : PosInt) :
    numDistinctPrimeFactors ⟨m.val * n.val, Nat.mul_pos m.property n.property⟩
      ≤ numDistinctPrimeFactors m + numDistinctPrimeFactors n := by
  classical
  have hm0 : m.val ≠ 0 := Nat.ne_of_gt m.property
  have hn0 : n.val ≠ 0 := Nat.ne_of_gt n.property
  have hpf :=
    Nat.primeFactors_mul (a := m.val) (b := n.val) hm0 hn0
  have hcard := Finset.card_union_le (Nat.primeFactors m.val) (Nat.primeFactors n.val)
  -- rewrite via hpf
  simpa [numDistinctPrimeFactors, hpf] using hcard
  /-
  証明戦略：
  1. primeFactors (m * n) ⊆ primeFactors m ∪ primeFactors n
  2. card (A ∪ B) ≤ card A + card B
  3. 包含関係からカード数の不等式が従う
  -/

/-- 素因数分解による構造塔

**層の構造**:
- layer 0 = {1}（素因数を持たない）
- layer 1 = {1, 2, 3, 5, 7, 11, ...}（1つ以下の素因数）
- layer 2 = {1, 2, 3, 4, 5, 6, 7, 10, 11, ...}（2つ以下の素因数）
- layer 3 = {1, 2, ..., 30, ...}（3つ以下の素因数）

**数論的性質**:
- layer 0 は乗法の単位元のみ
- layer 1 には素数とその冪が含まれる
- layer n には最大n個の異なる素数の積が含まれる
-/
def primeFactorTower : StructureTowerMin where
  carrier := PosInt
  layer n := { m : PosInt | numDistinctPrimeFactors m ≤ n }
  covering := by
    intro m
    refine ⟨numDistinctPrimeFactors m, ?_⟩
    dsimp
    exact le_rfl
  monotone := by
    intro i j hij m hm
    -- 展開してから単調性を適用
    exact le_trans hm hij
  minLayer := numDistinctPrimeFactors
  minLayer_mem := by
    intro m
    dsimp
    exact le_rfl
  minLayer_minimal := by
    intro m i hm
    dsimp at hm
    exact hm

/-! ### 具体的な計算例 -/

/-- 例1：1の最小層は0 -/
example : primeFactorTower.minLayer ⟨1, Nat.one_pos⟩ = 0 := by
  native_decide

/-- 例2：素数2の最小層は1 -/
example : primeFactorTower.minLayer ⟨2, by norm_num⟩ = 1 := by
  native_decide

/-- 例3：6 = 2 × 3 の最小層は2 -/
example : primeFactorTower.minLayer ⟨6, by norm_num⟩ = 2 := by
  native_decide

/-- 例4：30 = 2 × 3 × 5 の最小層は3 -/
example : primeFactorTower.minLayer ⟨30, by norm_num⟩ = 3 := by
  native_decide

/-! ### 層の構造に関する定理 -/

/-- Layer 0 は単位元のみ -/
theorem layer_zero_eq_one :
    primeFactorTower.layer 0 = {⟨1, Nat.one_pos⟩} := by
  classical
  ext m
  constructor
  · intro hm
    -- numDistinctPrimeFactors m ≤ 0 ⇒ card = 0
    have hzero : (Nat.primeFactors m.val).card = 0 :=
      Nat.eq_zero_of_le_zero hm
    have hpfset : Nat.primeFactors m.val = ∅ := Finset.card_eq_zero.mp hzero
    -- primeFactors = ∅ ⇒ m.val = 0 ∨ 1
    have hval : m.val = 0 ∨ m.val = 1 :=
      (Nat.primeFactors_eq_empty (n := m.val)).1 hpfset
    -- 0 は PosInt ではない
    have hv1 : m.val = 1 := by
      cases hval with
      | inl h0 => cases m.property.ne' h0
      | inr h1 => exact h1
    -- 目的の単位元に一致
    have hm1 : m = ⟨1, Nat.one_pos⟩ := Subtype.ext (by simpa using hv1)
    simp [primeFactorTower, hm1]
  · intro hm
    -- 1 は自明に layer 0 に入る
    rcases hm with rfl
    -- goal: numDistinctPrimeFactors 1 ≤ 0
    change numDistinctPrimeFactors ⟨1, Nat.one_pos⟩ ≤ 0
    native_decide

/-- Layer 1 には素数の冪が含まれる -/
theorem prime_power_in_layer_one (p : ℕ) (k : ℕ) (hp : Nat.Prime p) (hk : 0 < k) :
    ⟨p ^ k, by
      have h' : 0 < p ^ k := by exact pow_pos hp.pos k
      simpa using h'⟩
      ∈ primeFactorTower.layer 1 := by
  classical
  have hkne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hpf : (Nat.primeFactors (p ^ k)) = ({p} : Finset ℕ) :=
    Nat.primeFactors_prime_pow (k := k) hkne hp
  -- numDistinctPrimeFactors (p^k) = 1
  have hcard : numDistinctPrimeFactors ⟨p ^ k, by
      have h' : 0 < p ^ k := pow_pos hp.pos k
      simpa using h'⟩ = 1 := by
    simp [numDistinctPrimeFactors, hpf]
  -- membership in layer 1
  simpa [primeFactorTower, hcard] using (le_of_eq hcard)
  /-
  証明戦略：
  1. p^k の素因数はpのみ
  2. よって numDistinctPrimeFactors(p^k) = 1
  3. 1 ≤ 1 より p^k ∈ layer 1
  -/

/-- 数論的定理との対応：算術の基本定理 -/
theorem unique_factorization_via_minLayer (m : PosInt) :
    ∃! (ps : Finset ℕ), (∀ p ∈ ps, Nat.Prime p) ∧
      ps.card = primeFactorTower.minLayer m := by
  sorry
  /-
  証明戦略：
  1. ps := Nat.primeFactors m.val とする
  2. 一意分解定理より、この ps は一意
  3. ps.card = numDistinctPrimeFactors m = minLayer m

  **数論的意義**: minLayer は素因数分解の「一意性」を反映している
  -/

end PrimeFactorDepth

/-!
## 例2：約数の個数による階層

### 数論的背景

約数関数 d(n) は整数論の基本的な関数：
- d(1) = 1（1のみ）
- d(6) = 4（1, 2, 3, 6）
- d(12) = 6（1, 2, 3, 4, 6, 12）

### 構造塔としての定式化

- **carrier**: ℤ>0
- **layer n**: 約数が≤n個の正整数
- **minLayer(m)**: mの約数の個数

### 従来の数論との対応

- **約数関数**: d(n) = minLayer(n)
- **完全数**: d(n) = 2n となる n（特別な層）
- **高度合成数**: d(n) が最大となる n

### IUT理論への展望

約数の個数は、イデアル分解の複雑さに対応。
IUT理論では、イデアル構造の「高さ」を測る概念へ発展。
-/

namespace DivisorCount

/-- 正の整数 -/
def PosInt := { n : ℕ // 0 < n }

/-- 約数の個数

**定義**: nの正の約数の個数
**例**:
- numDivisors(1) = 1
- numDivisors(6) = 4（1, 2, 3, 6）
- numDivisors(12) = 6（1, 2, 3, 4, 6, 12）
-/
def numDivisors (n : PosInt) : ℕ :=
  (Nat.divisors n.val).card

/-! ### 基本補題 -/

lemma numDivisors_one : numDivisors ⟨1, Nat.one_pos⟩ = 1 := by
  simp [numDivisors, Nat.divisors_one]

lemma numDivisors_prime (p : ℕ) (hp : Nat.Prime p) :
    numDivisors ⟨p, hp.pos⟩ = 2 := by
  classical
  -- divisors of p are an image of range (1+1)
  have hcard : (Nat.divisors p).card = 2 := by
    have := congrArg Finset.card (Nat.divisors_prime_pow hp 1)
    -- divisors (p^1) = range (1+1) mapped, hence card = 2
    simpa [Nat.pow_one] using this
  simpa [numDivisors] using hcard

/-- 約数個数による構造塔 -/
def divisorTower : StructureTowerMin where
  carrier := PosInt
  layer n := { m : PosInt | numDivisors m ≤ n }
  covering := by
    intro m
    refine ⟨numDivisors m, ?_⟩
    dsimp
    exact le_rfl
  monotone := by
    intro i j hij m hm
    exact le_trans hm hij
  minLayer := numDivisors
  minLayer_mem := by intro m; dsimp; exact le_rfl
  minLayer_minimal := by intro m i hm; dsimp at hm; exact hm

/-! ### 計算例 -/

example : divisorTower.minLayer ⟨1, Nat.one_pos⟩ = 1 := by rfl

example : divisorTower.minLayer ⟨6, by norm_num⟩ = 4 := by
  native_decide  -- computable finite set

example : divisorTower.minLayer ⟨12, by norm_num⟩ = 6 := by
  native_decide

/-! ### 約数関数の性質 -/

/-- Layer 1 は1のみ -/
theorem layer_one_eq_singleton :
    divisorTower.layer 1 = {⟨1, Nat.one_pos⟩} := by
  classical
  ext m
  constructor
  · intro hm
    have hmpos : 0 < m.val := m.property
    have hcard : (Nat.divisors m.val).card ≤ 1 := hm
    have hpos : 0 < (Nat.divisors m.val).card := by
      have hmem : (1 : ℕ) ∈ Nat.divisors m.val :=
        Nat.mem_divisors.mpr ⟨Nat.one_dvd _, Nat.succ_le_of_lt hmpos⟩
      exact Finset.card_pos.mpr ⟨1, hmem⟩
    have hcard1 : (Nat.divisors m.val).card = 1 :=
      le_antisymm hcard (Nat.succ_le_iff.mpr hpos)
    obtain ⟨x, hxmem, hxuniq⟩ := Finset.card_eq_one.mp hcard1
    have h1mem : (1 : ℕ) ∈ Nat.divisors m.val :=
      Nat.mem_divisors.mpr ⟨Nat.one_dvd _, Nat.succ_le_of_lt hmpos⟩
    have hx1 : x = 1 := hxuniq h1mem
    have hmv_mem : m.val ∈ Nat.divisors m.val :=
      Nat.mem_divisors.mpr ⟨by rfl, Nat.succ_le_of_lt hmpos⟩
    have hmv1 : m.val = 1 := by
      have := hxuniq hmv_mem
      simpa [hx1] using this
    subst hmv1
    simp
  · intro hm
    rcases hm with rfl
    simp [divisorTower, numDivisors_one]

/-- Layer 2 には素数が含まれる -/
theorem prime_in_layer_two (p : ℕ) (hp : Nat.Prime p) :
    ⟨p, hp.pos⟩ ∈ divisorTower.layer 2 := by
  -- numDivisors p = 2 より
  have h := numDivisors_prime p hp
  -- layer 2 means numDivisors ≤ 2
  have : numDivisors ⟨p, hp.pos⟩ ≤ 2 := by simpa [h]
  exact this

end DivisorCount

/-!
## 例3：合同式の階層（mod 2^n）

### 数論的背景

整数環における合同関係の系列：
- ℤ/2ℤ（奇偶のみ区別）
- ℤ/4ℤ（4で割った余り）
- ℤ/8ℤ（8で割った余り）
- ...

これは「2-進付値」（2-adic valuation）の離散版。

### 構造塔としての定式化

- **carrier**: ℤ
- **layer n**: 2^n で割り切れる整数の集合
- **minLayer(m)**: mが初めて 0 でなくなる最小の n

### 数論的意義

- **p-進付値**: v₂(m) = max{k | 2^k | m}
- **Henselの補題**: p-進体における持ち上げ定理
- **局所体**: p-進数体の構造

### IUT理論への展望

p-進Hodge理論において、「p-進的な深さ」を測る概念へ発展。
IUT理論の中核概念「Hodge-Arakelov理論」の基礎。
-/

namespace CongruenceHierarchy

/-- 整数のmod 2^nによる階層 -/

/- 2-進付値：mが2^kで何回割り切れるか

**定義**: v₂(m) = max{k | 2^k | m}
**例**:
- twoPadicValuation(0) = ∞（便宜上大きな値）
- twoPadicValuation(1) = 0（奇数）
- twoPadicValuation(4) = 2（4 = 2²）
- twoPadicValuation(12) = 2（12 = 2² × 3）
-/
def twoPadicValuation (_m : ℤ) : ℕ :=
  -- 簡略化のため定数にしておく（本実装では Nat.find を用いる）
  0
  /-
  正確な実装には以下が必要：
  1. m ≠ 0 のとき、∃ k, ¬(2^k | m)（有限性）
  2. Nat.find でこの最小値を見つける
  3. 結果から1を引くと実際の付値

  ここでは教育的簡略化のため sorry
  -/

/-- 簡略版：小さな整数の2-進付値を直接定義 -/
def twoPadicValSimple (m : ℤ) : ℕ :=
  if m % 2 ≠ 0 then 0  -- 奇数
  else if m % 4 ≠ 0 then 1  -- 2で割り切れるが4では割り切れない
  else if m % 8 ≠ 0 then 2  -- 4で割り切れるが8では割り切れない
  else 3  -- 8以上で割り切れる（簡略化）

instance (n : ℕ) : DecidablePred (fun m : ℤ => twoPadicValSimple m ≤ n) :=
  fun m => Nat.decLe (twoPadicValSimple m) n

/-- 2-進付値による構造塔 -/
def congruenceTower : StructureTowerMin where
  carrier := ℤ
  layer n := { m : ℤ | twoPadicValSimple m ≤ n }
  covering := by
    intro m
    refine ⟨twoPadicValSimple m, ?_⟩
    dsimp
    exact le_rfl
  monotone := by
    intro i j hij m hm
    exact le_trans hm hij
  minLayer := twoPadicValSimple
  minLayer_mem := by intro m; dsimp; exact le_rfl
  minLayer_minimal := by intro m i hm; dsimp at hm; exact hm

/-! ### 計算例 -/

example : congruenceTower.minLayer (1 : ℤ) = 0 := by rfl  -- 奇数

example : congruenceTower.minLayer (2 : ℤ) = 1 := by
  native_decide  -- twoPadicValSimple 2 = 1

example : congruenceTower.minLayer (4 : ℤ) = 2 := by
  native_decide  -- twoPadicValSimple 4 = 2

/-! ### 数論的性質 -/

/-- Layer 0 は奇数全体 -/
theorem layer_zero_odd :
    congruenceTower.layer 0 = { m : ℤ | m % 2 ≠ 0 } := by
  ext m
  constructor
  · intro hm
    have hzero : twoPadicValSimple m = 0 := le_antisymm hm (Nat.zero_le _)
    dsimp [twoPadicValSimple] at hzero
    by_cases hodd : m % 2 ≠ 0
    · exact hodd
    · have : False := by
        -- if not odd, first branch impossible so contradiction
        simp [hodd] at hzero
      contradiction
  · intro hodd
    dsimp [congruenceTower, twoPadicValSimple]
    -- odd → first branch selected, so value = 0
    simp [hodd]

/-- 包含関係：2-進イデアル列 -/
theorem ideal_chain :
    ∀ n : ℕ, congruenceTower.layer n ⊆ congruenceTower.layer (n + 1) := by
  intro n m hm
  exact congruenceTower.monotone (Nat.le_succ n) hm

end CongruenceHierarchy

/-!
# 第2部：代数的整数論

この部では、二次体や円分体といった代数的構造の階層を扱う。
-/

/-!
## 例4：二次体のノルムによる階層

### 数論的背景

二次体 ℚ[√d] の元 a + b√d のノルムは：
- N(a + b√d) = a² - db²

これは整数値を取り、元の「大きさ」を測る。

### 構造塔としての定式化

- **carrier**: ℚ[√2] の元
- **layer n**: |N(α)| ≤ n なる α
- **minLayer(α)**: |N(α)|

### 数論的意義

- **単数群**: N(α) = ±1 なる α（layer 1）
- **イデアルのノルム**: 整数環のイデアル理論
- **類数**: イデアル類群の位数

### IUT理論への展望

代数的整数環の構造は、IUT理論における「数論的ホロノミー」の基礎。
-/

namespace QuadraticFieldNorm

/-- ℚ[√2] の元を (a, b) ∈ ℚ² で表現 -/
def QuadExt := ℚ × ℚ  -- a + b√2 を (a, b) で表現

/-- ノルム関数 N(a + b√2) = a² - 2b² -/
def norm (α : QuadExt) : ℚ :=
  α.1 * α.1 - 2 * α.2 * α.2

/-- ノルムの絶対値（整数部分） -/
def normAbs (α : QuadExt) : ℕ :=
  Int.natAbs (norm α).floor

/-- ノルム階層による構造塔

**注意**: これは簡略版。完全版では整数環に制限すべき。
-/
noncomputable def quadraticNormTower : StructureTowerMin where
  carrier := QuadExt
  layer n := { α : QuadExt | normAbs α ≤ n }
  covering := by
    intro α
    refine ⟨normAbs α, ?_⟩
    dsimp
    exact le_rfl
  monotone := by
    intro i j hij α hα
    exact le_trans hα hij
  minLayer := normAbs
  minLayer_mem := by intro α; dsimp; exact le_rfl
  minLayer_minimal := by intro α i hα; dsimp at hα; exact hα

/-! ### 計算例 -/

example : quadraticNormTower.minLayer (1, 0) = 1 := by
  simp [quadraticNormTower, normAbs, norm, Int.ofNat_eq_coe, Int.floor_coe]

example : quadraticNormTower.minLayer (0, 1) = 2 := by
  norm_num [quadraticNormTower, normAbs, norm]

example : quadraticNormTower.minLayer (3, 2) = 1 := by
  norm_num [quadraticNormTower, normAbs, norm]

end QuadraticFieldNorm

/-!
## 例5：円分体の拡大次数階層

### 数論的背景

円分体の塔：
- ℚ ⊆ ℚ[ζ₃] ⊆ ℚ[ζ₆] ⊆ ℚ[ζ₁₂] ⊆ ...

ここで ζₙ は1の原始n乗根。

### 構造塔としての定式化

- **carrier**: 代数的数
- **layer n**: [ℚ(α):ℚ] ≤ n なる α
- **minLayer(α)**: αの最小多項式の次数

### IUT理論への展望

円分体の塔は、IUT理論における「エタール基本群」の離散版。
-/

namespace CyclotomicExtension

/-- オイラーのφ関数（mathlib の `Nat.totient` を利用） -/
def eulerPhi (n : ℕ) : ℕ := Nat.totient n

/-- 円分拡大の次数

[ℚ[ζₙ]:ℚ] = φ(n)（オイラーのφ関数）
-/
def cyclotomicDegree (n : ℕ) : ℕ :=
  eulerPhi n

/-! ### 計算例（コメントとして） -/

/-
  cyclotomicDegree 1 = 1  -- ℚ[ζ₁] = ℚ
  cyclotomicDegree 2 = 1  -- ℚ[ζ₂] = ℚ
  cyclotomicDegree 3 = 2  -- ℚ[ζ₃] は2次拡大
  cyclotomicDegree 4 = 2  -- ℚ[ζ₄] = ℚ[i]
  cyclotomicDegree 6 = 2  -- ℚ[ζ₆] = ℚ[ζ₃]
-/

end CyclotomicExtension

/-!
# 第3部：体論の例

有限体の拡大列と代数拡大の階層を扱う。
-/

/-!
## 例6：有限体の拡大列

### 数論的背景

有限体の拡大列：
- 𝔽₂ ⊆ 𝔽₄ ⊆ 𝔽₁₆ ⊆ 𝔽₂₅₆ ⊆ ...
- [𝔽₂ₙ : 𝔽₂] = n

### 構造塔としての定式化

- **carrier**: 𝔽₂の代数的閉包の元
- **layer n**: 𝔽₂ₙ に含まれる元
- **minLayer(α)**: [𝔽₂(α):𝔽₂]

### IUT理論への展望

有限体の拡大は、「エタール拡大」の最も単純な例。
IUT理論では、これが「遠アーベル幾何」へ発展。
-/

namespace FiniteFieldExtension

/-- 𝔽₂の元を代表する型（簡略版） -/
inductive F2Elem : Type
  | zero : F2Elem
  | one : F2Elem

deriving instance DecidableEq for F2Elem

instance : Fintype F2Elem := by
  classical
  refine
    { elems := {F2Elem.zero, F2Elem.one}
      , complete := ?_ }
  intro x
  cases x <;> simp

/-- F2Elem のサイズは2 -/
lemma F2Elem_card : Fintype.card F2Elem = 2 := by
  -- finite type of two constructors
  decide

/-!
**教育的注意**:

完全な有限体の実装は Mathlib の Fintype を使うべきだが、
1年次学生の理解のため簡略化している。

実際の実装では：
- ZMod 2 を使う（𝔽₂）
- FiniteField 型クラスを使う
- Galois理論の結果を利用
-/

end FiniteFieldExtension

/-!
# 第4部：発展例 - 楕円曲線

楕円曲線の torsion points の階層（選択課題）
-/

/-!
## 例7：楕円曲線のtorsion points

### 数論的背景

楕円曲線 E/ℚ 上の有理点で、有限位数を持つもの：
- E[n] = {P ∈ E(ℚ) | nP = O}（n-torsion points）

### 構造塔としての定式化

- **carrier**: E(ℚ)（有理点）
- **layer n**: n-torsion points
- **minLayer(P)**: Pの位数

### IUT理論への展望

楕円曲線の torsion 構造は、IUT理論の中核：
- Hodge-Tate構造
- p-adic Teichmüller理論
- 楕円曲線の「宇宙際的」扱い

**注意**: この例は発展的で、完全な実装は高度な代数幾何を要する。
-/

namespace EllipticCurveTorsion

/-
楕円曲線の完全な実装は本課題の範囲を超えるため、
概念的な説明にとどめる。

興味ある学生は以下を参照：
- Silverman "The Arithmetic of Elliptic Curves"
- Mathlib の AlgebraicGeometry.EllipticCurve
-/

end EllipticCurveTorsion

/-!
# まとめと考察

## 構造塔による統一的視点

すべての例が以下のパターンに従う：

```lean
layer n = { x | f(x) ≤ n }
minLayer x = f(x)
```

ここで f は数論的不変量：
- 素因数の個数
- 約数の個数
- 2-進付値
- ノルムの絶対値
- 拡大次数
- torsion の位数

## Bourbakiの母構造思想との対応

本課題の例は、Bourbakiの3つの母構造に対応：

1. **代数的構造**: イデアル、体拡大、群の構造
2. **順序構造**: 層の包含関係 layer n ⊆ layer (n+1)
3. **（位相構造）**: 発展課題として p-進位相

構造塔は、これらを統一する「第4の母構造」と見ることができる。

## IUT理論への橋渡し

望月新一のIUT理論における重要概念：

1. **多重宇宙**: 各層が「異なる宇宙」に対応
2. **Θ-link**: 層の間の移行が「宇宙間の対応」
3. **Hodge-Arakelov理論**: p-進的な「深さ」の測定

本課題の minLayer は、これらの概念の離散的・初等的版である。

-/

/-!
## Report課題のヒント

### 課題1：minLayer の数論的意味

各例で minLayer が測っているものを比較せよ：
- 例1: 素因数の「種類数」（乗法的複雑さ）
- 例2: 約数の「個数」（除法的豊かさ）
- 例3: 2-進的「深さ」（局所的構造）
- 例4: ノルムの「大きさ」（体の構造）

### 課題2：層の包含関係

layer n ⊆ layer (n+1) が真に狭義になる条件：
- 例1: n+1個の異なる素因数を持つ数が存在するか？
- 例2: ちょうど n+1個の約数を持つ数は無限に存在

### 課題3：構造塔の公理の自然性

なぜ covering, monotone, minLayer_minimal が自然か？
- covering: すべての数論的対象は「有限の複雑さ」
- monotone: 「より複雑」は「より多くを含む」
- minLayer_minimal: 「最小」の明確な定義

-/

/-!
## Group Work課題のヒント

### 議論の出発点

1. すべての例で `layer n = { x | f(x) ≤ n }` の形
   → f の共通性質は何か？（単調性？加法性？）

2. minLayer が測る「複雑さ」とは？
   → 生成、分解、構成の「段階数」

3. IUT論文の「宇宙」との対応
   → 各層 = 1つの宇宙
   → 層の移行 = 宇宙間の対応

### グループワーク成功の鍵

- 具体例で計算しながら議論
- 数式だけでなく図を描く
- 「なぜ」を問い続ける

-/

end NumberTheoryTowers

/-!
## 追加課題（選択）

興味ある学生は以下にも挑戦せよ：

1. **他の素数での階層**: 3-進付値、5-進付値での構造塔
2. **イデアルのノルム**: 整数環のイデアルによる階層
3. **ガロア拡大の階層**: ガロア群の位数による分類
4. **高度合成数**: 約数が最大の数の特徴付け

これらは Report の追加点として評価される。
-/

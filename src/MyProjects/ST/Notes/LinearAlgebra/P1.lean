import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# ZEN大学「線形代数1」構造塔演習課題

このファイルは、線形代数の基礎概念を構造塔理論の観点から学ぶための演習課題です。

## 学習目標
1. 2次元有理ベクトル空間の基本操作を理解する
2. ベクトルを「必要な基底数」で階層化する概念を習得する
3. 線形写像が構造を保存することを証明する

## 課題の構成
- 基本レベル（Exercise 1-3）: ベクトルの定義と基本操作
- 中級レベル（Exercise 4-6）: minBasisCountの計算と層の構造
- 応用レベル（Exercise 7-10）: 構造塔の性質と線形写像
-/

namespace ZENUniversity.LinearAlgebra

/-! ## 第1部：基本定義（完全実装済み） -/

/-- 2次元有理ベクトル空間の元
これは、有理数を成分とする2次元ベクトルを表します。
-/
def Vec2Q : Type := ℚ × ℚ

namespace Vec2Q

/-- ベクトルの加法
(a, b) + (c, d) = (a+c, b+d)
-/
def add (v w : Vec2Q) : Vec2Q :=
  (v.1 + w.1, v.2 + w.2)

/-- スカラー倍
r · (a, b) = (r·a, r·b)
-/
def smul (r : ℚ) (v : Vec2Q) : Vec2Q :=
  (r * v.1, r * v.2)

/-- 零ベクトル -/
def zero : Vec2Q := (0, 0)

/-- 標準基底ベクトル e₁ = (1, 0) -/
def e1 : Vec2Q := (1, 0)

/-- 標準基底ベクトル e₂ = (0, 1) -/
def e2 : Vec2Q := (0, 1)

/-- 二つのベクトルが等しい
成分ごとの等式で定義される
-/
def eq (v w : Vec2Q) : Prop :=
  v.1 = w.1 ∧ v.2 = w.2

end Vec2Q

/-! ## 第2部：最小基底数の定義（完全実装済み） -/

/-- ベクトルを表現するのに必要な最小の標準基底ベクトル数

これは構造塔における minLayer 関数の具体例です：
- minBasisCount((0, 0)) = 0  （零ベクトル：基底不要）
- minBasisCount((a, 0)) = 1  （a ≠ 0: e₁のみ必要）
- minBasisCount((0, b)) = 1  （b ≠ 0: e₂のみ必要）
- minBasisCount((a, b)) = 2  （a, b ≠ 0: 両方の基底が必要）
-/
noncomputable def minBasisCount (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0
  else if v.1 = 0 ∨ v.2 = 0 then 1
  else 2

lemma minBasisCount_eq_zero_iff (v : Vec2Q) :
    minBasisCount v = 0 ↔ v = Vec2Q.zero := by
  constructor
  · intro h
    rcases v with ⟨a, b⟩
    unfold minBasisCount at h
    by_cases h0 : a = 0 ∧ b = 0
    · exact Prod.ext h0.1 h0.2
    · have h' : (if a = 0 ∨ b = 0 then 1 else 2) = 0 := by
        simpa [h0] using h
      by_cases h1 : a = 0 ∨ b = 0
      · simp [h1] at h'
      · simp [h1] at h'
  · intro hv
    subst hv
    simp [Vec2Q.zero, minBasisCount]

lemma minBasisCount_le_two (v : Vec2Q) : minBasisCount v ≤ 2 := by
  unfold minBasisCount
  by_cases h0 : v.1 = 0 ∧ v.2 = 0
  · simp [h0]
  · by_cases h1 : v.1 = 0 ∨ v.2 = 0
    · simp [h0, h1]
    · simp [h0, h1]

/-! ## 第3部：構造塔の定義（完全実装済み） -/

/-- 構造塔の簡易版定義

これは CAT2_complete.lean の StructureTowerWithMin を簡略化したものです。
-/
structure SimpleTowerWithMin where
  /-- 基礎集合 -/
  carrier : Type
  /-- 添字集合（階層を表す自然数） -/
  Index : Type
  /-- 添字集合上の半順序 -/
  [indexPreorder : Preorder Index]
  /-- 各層の定義: Index → Set carrier -/
  layer : Index → Set carrier
  /-- 被覆性: すべての要素がどこかの層に属する -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- 単調性: 順序を保存 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- 各要素の最小層を選ぶ関数 -/
  minLayer : carrier → Index
  /-- minLayer x は実際に x を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayer x は最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

/-- 2次元有理ベクトル空間上の線形包構造塔

層 n = {v ∈ ℚ² | minBasisCount(v) ≤ n}
として定義される構造塔の完全実装
-/
noncomputable def linearSpanTower : SimpleTowerWithMin where
  carrier := Vec2Q
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {v : Vec2Q | minBasisCount v ≤ n}
  covering := by
    intro v
    use minBasisCount v
    simp
  monotone := by
    intro i j hij v hv
    exact le_trans hv hij
  minLayer := minBasisCount
  minLayer_mem := by
    intro v
    show minBasisCount v ≤ minBasisCount v
    exact le_rfl
  minLayer_minimal := by
    intro v i hv
    exact hv

/-! ### Sanity checks -/

/-- `Vec2Q.zero` belongs to layer `0`. -/
example : Vec2Q.zero ∈ linearSpanTower.layer (0 : ℕ) := by
  change minBasisCount Vec2Q.zero ≤ (0 : ℕ)
  simp [Vec2Q.zero, minBasisCount]

/-! ## 演習問題 -/

/-! ### 基本レベル（Exercise 1-3） -/

/-- **Exercise 1**: ベクトル加法の可換性

零ベクトルの定義と加法を使って、可換性を証明してください。
ヒント: Vec2Q.add の定義を展開し、成分ごとに有理数の可換性を使います。
-/
lemma vec_add_comm (v w : Vec2Q) :
    Vec2Q.add v w = Vec2Q.add w v := by
  rcases v with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  apply Prod.ext <;> simp [Vec2Q.add, add_comm]

/-- **Exercise 2**: 零ベクトルは加法の単位元

任意のベクトル v に対して、v + 0 = v を示してください。
ヒント: 有理数の加法の単位元の性質を使います。
-/
lemma vec_add_zero (v : Vec2Q) :
    Vec2Q.add v Vec2Q.zero = v := by
  rcases v with ⟨a, b⟩
  apply Prod.ext <;> simp [Vec2Q.add, Vec2Q.zero]

/-- **Exercise 3**: スカラー倍の分配法則

スカラー r に対して、r · (v + w) = r · v + r · w を示してください。
ヒント: Vec2Q.smul と Vec2Q.add の定義を展開し、有理数の分配法則を使います。
-/
lemma smul_add_distrib (r : ℚ) (v w : Vec2Q) :
    Vec2Q.smul r (Vec2Q.add v w) =
    Vec2Q.add (Vec2Q.smul r v) (Vec2Q.smul r w) := by
  rcases v with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  apply Prod.ext <;> simp [Vec2Q.add, Vec2Q.smul, mul_add]

/-! ### 中級レベル（Exercise 4-6） -/

/-- **Exercise 4**: 零ベクトルの最小基底数

零ベクトル (0, 0) の最小基底数が 0 であることを示してください。
ヒント: minBasisCount の定義を unfold して、if 文の条件を確認します。
-/
lemma minBasisCount_zero :
    minBasisCount Vec2Q.zero = 0 := by
  simp [Vec2Q.zero, minBasisCount]

/-- **Exercise 5**: x軸上のベクトルの最小基底数

a ≠ 0 のとき、ベクトル (a, 0) の最小基底数が 1 であることを示してください。
ヒント: minBasisCount の定義で、第二成分が 0 の場合を考えます。
-/
lemma minBasisCount_x_axis (a : ℚ) (ha : a ≠ 0) :
    minBasisCount (a, 0) = 1 := by
  simp [minBasisCount, ha]

/-- **Exercise 6**: 一般位置のベクトルの最小基底数

a ≠ 0 かつ b ≠ 0 のとき、ベクトル (a, b) の最小基底数が 2 であることを示してください。
ヒント: minBasisCount の定義で、両成分が非零の場合を考えます。
-/
lemma minBasisCount_general (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    minBasisCount (a, b) = 2 := by
  simp [minBasisCount, ha, hb]

/-! ### 応用レベル（Exercise 7-10） -/

/-- **Exercise 7**: 層の包含関係

層 0 は層 1 に含まれることを示してください。
ヒント: linearSpanTower.monotone を使用します。
-/
theorem layer_0_subset_layer_1 :
    linearSpanTower.layer (0 : ℕ) ⊆ linearSpanTower.layer (1 : ℕ) := by
  simpa using
    linearSpanTower.monotone (i := (0 : ℕ)) (j := (1 : ℕ)) (Nat.zero_le 1)

/-- **Exercise 8**: 層 0 の完全な特徴付け

層 0 は零ベクトルのみからなることを示してください。
ヒント: v ∈ layer 0 ⇔ minBasisCount(v) ≤ 0 ⇔ minBasisCount(v) = 0
-/
theorem layer_0_characterization :
    linearSpanTower.layer (0 : ℕ) = {Vec2Q.zero} := by
  ext v
  constructor
  · intro hv
    have hv0 : minBasisCount v ≤ (0 : ℕ) := by
      simpa [linearSpanTower] using hv
    have hv_eq : v = Vec2Q.zero :=
      (minBasisCount_eq_zero_iff v).1 (Nat.eq_zero_of_le_zero hv0)
    simpa using hv_eq
  · intro hv
    have hv_eq : v = Vec2Q.zero := by simpa using hv
    subst hv_eq
    simp [linearSpanTower, Vec2Q.zero, minBasisCount]

/-- **Exercise 9**: 層 1 の特徴付け

層 1 は座標軸上のベクトル（零ベクトルを含む）からなることを示してください。
ヒント: v ∈ layer 1 ⇔ v.1 = 0 または v.2 = 0
-/
theorem layer_1_characterization :
    linearSpanTower.layer (1 : ℕ) = {v : Vec2Q | v.1 = 0 ∨ v.2 = 0} := by
  ext v
  rcases v with ⟨a, b⟩
  change minBasisCount (a, b) ≤ (1 : ℕ) ↔ a = 0 ∨ b = 0
  constructor
  · intro hv
    by_contra h'
    have ha : a ≠ 0 := by
      intro ha0
      exact h' (Or.inl ha0)
    have hb : b ≠ 0 := by
      intro hb0
      exact h' (Or.inr hb0)
    have hcount : minBasisCount (a, b) = 2 := by
      simp [minBasisCount, ha, hb]
    have hv' := hv
    simp [hcount] at hv'
  · intro h
    cases h with
    | inl ha0 =>
      by_cases hb0 : b = 0
      · simp [minBasisCount, ha0, hb0]
      · simp [minBasisCount, ha0, hb0]
    | inr hb0 =>
      by_cases ha0 : a = 0
      · simp [minBasisCount, ha0, hb0]
      · simp [minBasisCount, ha0, hb0]

/-- **Exercise 10**: スカラー倍は minLayer を保存する

非零スカラー r に対して、スカラー倍写像 v ↦ r · v は
minBasisCount を保存することを示してください。

これは、スカラー倍が構造塔の射であることの証明の一部です。
ヒント: v の成分で場合分けし、r ≠ 0 を使って
  r · a ≠ 0 ⇔ a ≠ 0 を示します。
-/
theorem smul_preserves_minLayer (r : ℚ) (hr : r ≠ 0) (v : Vec2Q) :
    minBasisCount (Vec2Q.smul r v) = minBasisCount v := by
  rcases v with ⟨a, b⟩
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [Vec2Q.smul, minBasisCount, ha, hb]
    · have hrb : r * b ≠ 0 := mul_ne_zero hr hb
      simp [Vec2Q.smul, minBasisCount, ha, hb, hrb]
  · by_cases hb : b = 0
    · have hra : r * a ≠ 0 := mul_ne_zero hr ha
      simp [Vec2Q.smul, minBasisCount, ha, hb, hra]
    · have hra : r * a ≠ 0 := mul_ne_zero hr ha
      have hrb : r * b ≠ 0 := mul_ne_zero hr hb
      simp [Vec2Q.smul, minBasisCount, ha, hb, hra, hrb]

/-! ## 発展課題（オプション） -/

/-- **Challenge 1**: 層 2 以降の特徴付け

n ≥ 2 のとき、層 n は ℚ² 全体に等しいことを示してください。
-/
theorem layer_ge_2_is_full (n : ℕ) (hn : n ≥ 2) :
    linearSpanTower.layer n = Set.univ := by
  ext v
  constructor
  · intro _
    simp
  · intro _
    have hv : minBasisCount v ≤ 2 := minBasisCount_le_two v
    have : minBasisCount v ≤ n := le_trans hv hn
    simpa [linearSpanTower] using this

/-- **Challenge 2**: ベクトル加法と minBasisCount

一般に、minBasisCount(v + w) ≤ max(minBasisCount(v), minBasisCount(w)) + 1
が成り立つことを示してください。

ヒント: これは線形独立性の性質を反映しています。
-/
theorem minBasisCount_add_le (v w : Vec2Q) :
    minBasisCount (Vec2Q.add v w) ≤
    max (minBasisCount v) (minBasisCount w) + 1 := by
  by_cases hmax : max (minBasisCount v) (minBasisCount w) = 0
  · have hv0 : v = Vec2Q.zero := by
      have hvle : minBasisCount v ≤ (0 : ℕ) := by
        have : minBasisCount v ≤ max (minBasisCount v) (minBasisCount w) := by
          exact le_max_left _ _
        simpa [hmax] using this
      exact (minBasisCount_eq_zero_iff v).1 (Nat.eq_zero_of_le_zero hvle)
    have hw0 : w = Vec2Q.zero := by
      have hwle : minBasisCount w ≤ (0 : ℕ) := by
        have : minBasisCount w ≤ max (minBasisCount v) (minBasisCount w) := by
          exact le_max_right _ _
        simpa [hmax] using this
      exact (minBasisCount_eq_zero_iff w).1 (Nat.eq_zero_of_le_zero hwle)
    subst hv0
    subst hw0
    simp [Vec2Q.add, Vec2Q.zero, minBasisCount]
  · have hv : minBasisCount (Vec2Q.add v w) ≤ 2 := minBasisCount_le_two _
    have hpos : 0 < max (minBasisCount v) (minBasisCount w) :=
      Nat.pos_of_ne_zero hmax
    have hone : (1 : ℕ) ≤ max (minBasisCount v) (minBasisCount w) :=
      Nat.succ_le_iff.2 hpos
    have htwo : (2 : ℕ) ≤ max (minBasisCount v) (minBasisCount w) + 1 := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_le_succ hone
    exact le_trans hv htwo

/-! ## 補助定義：3次元への拡張 -/

/-- 3次元有理ベクトル空間（発展課題用） -/
def Vec3Q : Type := ℚ × ℚ × ℚ

/-- Vec3Q の最小基底数
3次元への自然な拡張
-/
noncomputable def minBasisCount3 (v : Vec3Q) : ℕ :=
  if v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2 = 0 then 0
  else if (v.1 = 0 ∧ v.2.1 = 0) ∨ (v.1 = 0 ∧ v.2.2 = 0) ∨ (v.2.1 = 0 ∧ v.2.2 = 0) then 1
  else if v.1 = 0 ∨ v.2.1 = 0 ∨ v.2.2 = 0 then 2
  else 3

/-- **Challenge 3**: 3次元構造塔の構成

Vec3Q 上に linearSpanTower3 を構成してください。
定義は完全実装する必要があります（sorry 禁止）。
-/
noncomputable def linearSpanTower3 : SimpleTowerWithMin where
  carrier := Vec3Q
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {v : Vec3Q | minBasisCount3 v ≤ n}
  covering := by
    intro v
    use minBasisCount3 v
    simp
  monotone := by
    intro i j hij v hv
    exact le_trans hv hij
  minLayer := minBasisCount3
  minLayer_mem := by
    intro v
    show minBasisCount3 v ≤ minBasisCount3 v
    exact le_rfl
  minLayer_minimal := by
    intro v i hv
    exact hv

end ZENUniversity.LinearAlgebra

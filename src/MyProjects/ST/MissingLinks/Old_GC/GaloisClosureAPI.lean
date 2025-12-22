import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic

/-!
# 生成⇄閉包のガロア接続：構造塔理論の統一基盤

このファイルは、構造塔理論の「Missing Link」として、ガロア接続を最上位概念に据えた
統一的フレームワークを提供する。

## 理論的階層構造

```
ガロア接続 (Gen ⊣ Cl)          ← 最上位：随伴関手の関係
    ↓ 導出
閉包演算子の性質               ← 単調性・拡大性・冪等性
    ↓ 誘導
反復回数による塔               ← iteration count tower
    ↓ インスタンス化
StructureTowerWithMin          ← 既存の塔定義
    ↓ 具体例
線形包・部分群・停止時刻        ← 数学的応用
```

## 数学的背景

### ガロア接続の定義
部分順序集合 (P, ≤) と (Q, ≤) の間の2つの単調写像 f : P → Q と g : Q → P が
**ガロア接続** (Galois connection) を成すとは：

```
∀ p : P, ∀ q : Q, f(p) ≤ q ↔ p ≤ g(q)
```

### 生成⇄閉包の随伴性

- **Gen** : Set α → S （生成関数：部分集合から部分構造へ）
- **Cl** : S → Set α （閉包関数：部分構造の台集合）

ガロア接続: `Gen(s) ≤ t ↔ s ⊆ Cl(t)`

直観的意味：
- 左から右：「s が t を生成する」⇒「s は t の台集合に含まれる」
- 右から左：「s が t に含まれる」⇒「s から生成される構造は t 以下」

### 余モナド構造

閉包演算子は余モナド (comonad) の構造を持つ：
- **counit** : Cl ∘ Gen → id（生成して閉包を取れば元に戻る）
- **comultiplication** : Cl → Cl ∘ Cl ∘ Cl（閉包の冪等性）

## 主要な定理

1. **閉包の等冪性導出**：ガロア接続から `Cl ∘ Cl = Cl` が従う
2. **反復回数塔の構成**：ガロア接続から自然に iteration count tower が誘導される
3. **minLayer の特徴づけ**：`minLayer(x) = min {|s| : x ∈ Cl(Gen(s))}`

Note: `S` is assumed to carry a `Preorder` so that the Galois connection and monotonicity
statements are well-typed.

-/

/-! ## Part 1: ガロア接続の基本型クラス -/

namespace GaloisClosure

/--
生成⇄閉包のガロア接続を表現する型クラス。

- `α`: 基礎集合（元の型）
- `S`: 部分構造の型（例：部分空間、部分群、停止時刻）

数学的に、これは以下の随伴関手対に対応：
```
Gen : Set α ⇄ S : Forget
```
-/
class GeneratorClosureGC (α : Type*) (S : Type*) [Preorder S] where
  /-- 生成関数：部分集合から部分構造を生成 -/
  gen : Set α → S

  /-- 閉包関数：部分構造の台集合（underlying set）を取る -/
  cl : S → Set α

  /-- Gen と Cl はガロア接続を成す -/
  gc : GaloisConnection gen cl

  /-- 閉包の単調性（ガロア接続から導出可能だが明示） -/
  cl_mono : Monotone cl

export GeneratorClosureGC (gen cl gc cl_mono)

/-! ## Part 2: ガロア接続から導出される基本性質 -/

section BasicProperties

variable {α : Type*} {S : Type*} [Preorder S] [GeneratorClosureGC α S]

/--
**拡大性（Extensivity）**：集合 s は、それが生成する構造の台集合に含まれる。

これは「生成」の直観に合致する基本性質。
-/
theorem subset_cl_gen (s : Set α) :
    s ⊆ cl (α := α) (S := S) (gen (α := α) (S := S) s) := by
  -- ガロア接続の左随伴の余単位（counit）から従う
  simpa using (GeneratorClosureGC.gc (α := α) (S := S)).le_u_l s

/--
**単調性（Monotonicity）**：小さい集合から生成される構造は小さい。

証明：ガロア接続の左随伴は単調。
-/
theorem gen_mono {s t : Set α} (h : s ⊆ t) :
    gen (α := α) (S := S) s ≤ gen (α := α) (S := S) t := by
  exact (GeneratorClosureGC.gc (α := α) (S := S)).monotone_l h

/--
**閉包の冪等性（Idempotence）**：閉包を2回取っても変わらない。

これは余モナドの comultiplication の退化した形。
-/
theorem cl_cl_eq (t : S) :
    cl (α := α) (S := S) (gen (α := α) (S := S) (cl (α := α) (S := S) t)) =
      cl (α := α) (S := S) t := by
  simpa using (GeneratorClosureGC.gc (α := α) (S := S)).u_l_u_eq_u t

/--
閉包演算子の等冪性の別形式：`cl t ⊆ cl s → cl (gen (cl t)) ⊆ cl s`
-/
theorem cl_gen_cl_subset {s t : S} (h : cl (α := α) (S := S) t ⊆ cl (α := α) (S := S) s) :
    cl (α := α) (S := S) (gen (α := α) (S := S) (cl (α := α) (S := S) t)) ⊆
      cl (α := α) (S := S) s := by
  rw [cl_cl_eq]
  exact h

end BasicProperties

/-! ## Part 3: 反復回数による塔の構成 -/

section IterationTower

variable {α : Type*} {S : Type*} [Preorder S] [GeneratorClosureGC α S]

/--
**反復閉包関数**：n回の生成⇄閉包操作を反復する。

直観：
- `iter 0 s = s`（何もしない）
- `iter 1 s = cl (gen s)`（一度生成して閉包）
- `iter 2 s = cl (gen (cl (gen s)))`（二重反復）

注意：`cl_cl_eq` により、`iter n` は `n` 回以降は安定する。
-/
def closureIter : ℕ → Set α → Set α
  | 0 => id
  | n + 1 => fun s => cl (α := α) (S := S) (gen (α := α) (S := S) (closureIter n s))

/--
反復の単調性：n ≤ m ならば iter n ⊆ iter m
-/
theorem closureIter_mono (s : Set α) {n m : ℕ} (h : n ≤ m) :
    closureIter (α := α) (S := S) n s ⊆ closureIter (α := α) (S := S) m s := by
  induction h with
  | refl => exact subset_refl _
  | @step m h ih =>
    apply Set.Subset.trans ih
    have hm :
        closureIter (α := α) (S := S) m s ⊆
          closureIter (α := α) (S := S) (Nat.succ m) s := by
      -- unfold one step and apply extensivity
      dsimp [closureIter]
      exact subset_cl_gen (α := α) (S := S) (closureIter (α := α) (S := S) m s)
    exact hm

/--
Iterating `cl ∘ gen` stabilizes once idempotence holds.

In fact, `closureIter` is constant from level `1`.
-/
theorem closureIter_eventually_constant (s : Set α) :
    ∃ N : ℕ, ∀ n ≥ N,
      closureIter (α := α) (S := S) n s = closureIter (α := α) (S := S) N s := by
  refine ⟨1, ?_⟩
  intro n hn
  have h_idem :
      cl (α := α) (S := S)
          (gen (α := α) (S := S) (closureIter (α := α) (S := S) 1 s)) =
        closureIter (α := α) (S := S) 1 s := by
    dsimp [closureIter]
    exact cl_cl_eq (α := α) (S := S) (gen (α := α) (S := S) s)
  have hstable :
      ∀ k : ℕ,
        closureIter (α := α) (S := S) (k + 1) s =
          closureIter (α := α) (S := S) 1 s := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        closureIter (α := α) (S := S) (k + 2) s =
            cl (α := α) (S := S)
              (gen (α := α) (S := S)
                (closureIter (α := α) (S := S) (k + 1) s)) := by
          rfl
        _ =
            cl (α := α) (S := S)
              (gen (α := α) (S := S)
                (closureIter (α := α) (S := S) 1 s)) := by
          simp [ih]
        _ = closureIter (α := α) (S := S) 1 s := h_idem
  cases n with
  | zero =>
    exact (False.elim (Nat.not_succ_le_zero 0 hn))
  | succ n =>
    simp [hstable n]

/--
**反復回数による層の定義**：n回以内の反復で到達可能な元の集合。

これが「iteration count tower」の各層を与える。
-/
def iterLayer (n : ℕ) : Set α :=
  {x : α | ∃ s : Set α, s.Finite ∧ x ∈ closureIter (α := α) (S := S) n s}

/--
層の単調性：n ≤ m ならば layer n ⊆ layer m
-/
theorem iterLayer_mono {n m : ℕ} (h : n ≤ m) :
    iterLayer (α := α) (S := S) n ⊆ iterLayer (α := α) (S := S) m := by
  intro x ⟨s, hs_fin, hx⟩
  exact ⟨s, hs_fin, closureIter_mono (α := α) (S := S) s h hx⟩

end IterationTower

/-! ## Part 4: 生成子数による塔の構成 -/

section GeneratorCountTower

variable {α : Type*} {S : Type*} [Preorder S] [GeneratorClosureGC α S]

/--
**(Deprecated)** Generator-count layer using `Set.ncard`.

This definition treats infinite sets as `ncard = 0`, which can be misleading.
Prefer the Finset-based `genCountLayer`.
-/
@[deprecated
  "Use genCountLayer (Finset-based). This version uses Set.ncard and can be misleading for infinite sets."
  (since := "2025-12-22")]
def genCountLayer_ncard (n : ℕ) : Set α :=
  {x : α | ∃ s : Set α, s.ncard ≤ n ∧
    x ∈ cl (α := α) (S := S) (gen (α := α) (S := S) s)}

/--
**Generator-count layer (Finset-based)**: elements generated by at most `n` generators.

This version is finite by construction and avoids the `Set.ncard` infinite-set pitfall.
-/
def genCountLayer (n : ℕ) : Set α := by
  classical
  exact {x : α | ∃ s : Finset α, s.card ≤ n ∧
    x ∈ cl (α := α) (S := S) (gen (α := α) (S := S) (s : Set α))}

/--
生成子数の層は単調。
-/
theorem genCountLayer_mono {n m : ℕ} (h : n ≤ m) :
    genCountLayer (α := α) (S := S) n ⊆ genCountLayer (α := α) (S := S) m := by
  intro x ⟨s, hs_card, hx⟩
  exact ⟨s, le_trans hs_card h, hx⟩

/-- Finset-based `genCountLayer` implies the deprecated `Set.ncard`-based layer. -/
theorem genCountLayer_subset_ncard (n : ℕ) :
    genCountLayer (α := α) (S := S) n ⊆ genCountLayer_ncard (α := α) (S := S) n := by
  classical
  intro x ⟨s, hs_card, hx⟩
  refine ⟨(s : Set α), ?_, hx⟩
  simpa [Set.ncard_coe_finset] using hs_card

/--
反復回数の層と生成子数の層の関係（概念的）。

完全な証明には具体的な構造の性質が必要。
-/
theorem genCountLayer_subset_iterLayer (n : ℕ) :
    genCountLayer (α := α) (S := S) n ⊆ iterLayer (α := α) (S := S) n := by
  sorry  -- TODO: reason="needs a concrete bridge from n generators to n iterations",
         -- follow-up="prove by constructing a finite generating set and iterating cl∘gen"

end GeneratorCountTower

/-! ## Part 5: ガロア接続から StructureTowerWithMin への射影 -/

section ToStructureTower

open Classical
attribute [local instance] Classical.propDecidable

/-- 最小層を持つ構造塔（添字は ℕ に固定した簡約版）の再定義 -/
structure StructureTowerWithMin where
  carrier : Type*
  layer : ℕ → Set carrier
  covering : ∀ x : carrier, ∃ i : ℕ, x ∈ layer i
  monotone : ∀ {i j : ℕ}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

variable {α : Type*} {S : Type*} [Preorder S] [GeneratorClosureGC α S]

/--
**ガロア接続から構造塔を構成**：生成子数による層を使う。

この構成により、ガロア接続は構造塔の「上流」概念となる。
-/
noncomputable def structureTowerFromGC
    (h_covers : ∀ x : α, ∃ n : ℕ, x ∈ genCountLayer (α := α) (S := S) n) :
    StructureTowerWithMin := by
  classical
  refine
    { carrier := α
      layer := genCountLayer (α := α) (S := S)
      covering := h_covers
      monotone := fun hij => genCountLayer_mono (α := α) (S := S) hij
      minLayer := fun x => Nat.find (h_covers x)
      minLayer_mem := fun x => Nat.find_spec (h_covers x)
      minLayer_minimal := fun x i hx => Nat.find_min' (h_covers x) hx }

/--
構成した塔の minLayer の意味：「元 x を生成するのに必要な最小の生成子数」
-/
theorem minLayer_characterization
    (h_covers : ∀ x : α, ∃ n : ℕ, x ∈ genCountLayer (α := α) (S := S) n) (x : α) :
    (structureTowerFromGC h_covers).minLayer x =
      Nat.find (h_covers x) := rfl

end ToStructureTower

/-! ## Part 6: 教育用の可視化と例 -/

section Visualization

/-!
### 理論的階層の可視化

```
Level 5: 随伴関手論
         Gen ⊣ Forget
            ↓
Level 4: ガロア接続
         Gen(s) ≤ t ↔ s ⊆ Cl(t)
            ↓
Level 3: 閉包演算子
         Cl : monotone, extensive, idempotent
            ↓
Level 2: 反復/生成子数による塔
         layer n = {x | 生成に必要な元の数 ≤ n}
            ↓
Level 1: StructureTowerWithMin
         minLayer(x) = 最小生成子数
            ↓
Level 0: 具体例
         線形包、部分群、停止時刻
```

### 直観的理解のための対応表

| 数学的概念        | 線形包の例                      | 停止時刻の例              |
|-------------------|--------------------------------|--------------------------|
| Gen(s)            | span(s)（線形包）              | σ(F_τ)（生成σ代数）      |
| Cl(t)             | t の台集合                     | 可測集合                 |
| ガロア接続        | span(s) ⊆ V ↔ s ⊆ V           | σ(F_τ) ⊆ F ↔ τ は F-可測 |
| closureIter n s   | n個のベクトルで生成            | n段階のσ代数             |
| genCountLayer n   | generated by ≤ n elements     | determined by ≤ n events |
| minLayer(x)       | x の表現に必要な最小基底数     | τ の決定に必要な最小段階 |
-/

end Visualization

end GaloisClosure

/-! ## DoD（完了条件）の検証用スケルトン -/

namespace VerificationExamples

/-!
以下の example を実装することで、理論の健全性を検証する：

1. 線形包のガロア接続インスタンス
2. 既存の minBasisCount が新フレームワークで再現されること
3. 閉包の等冪性が gc から導出されること
-/

-- TODO: 具体例の実装（次のファイルで行う）

end VerificationExamples

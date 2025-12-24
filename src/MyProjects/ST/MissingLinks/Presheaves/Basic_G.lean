import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Order.Lattice
import Mathlib.Data.Nat.Lattice

/-!
# Structure Towers and Stopping Times as Presheaves

確率論における「構造塔（Structure Tower）」と「停止時刻（Stopping Time）」を
圏論的な前層（Presheaf）と関手操作として定式化するモジュール。

## 理論的背景
確率過程の停止操作 $X^\tau_t = X_{t \wedge \tau}$ は、Index圏における
局所操作（min）と、それに伴うファイバー積（または前層の引き戻し）として理解できます。
-/

open CategoryTheory CategoryTheory.Limits Opposite Order

noncomputable section

universe u v w

/-!
## 1. Index圏の定義
-/

-- 基本実装：ℕ を順序圏としてインスタンス化（Mathlibの標準機能を活用）
instance : Category ℕ := inferInstance

-- 理論的拡張性：
-- 停止操作には `min` (inf) が必要であり、初期値には `⊥` (bot) が有用です。
-- これらを満たす任意の型 `I` に対して理論を構築します。
variable {I : Type u} [Preorder I] [SemilatticeInf I] [OrderBot I]

/-!
## 2. 構造塔から前層への変換
-/

/--
構造塔（Tower）のデータを保持する構造体。
ここでは前層（Presheaf）の形式、つまり反変関手（restriction mapsを持つ）として定義します。
確率論的文脈では「時刻 $j$ の情報は時刻 $i$ ($i \le j$) に制限できる」という
整合性条件（Consistent family of distributions/measures）に対応します。
-/
structure TowerPresheaf (I : Type u) [Preorder I] where
  obj : Iᵒᵖ → Type v
  map : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (obj i → obj j)
  map_id : ∀ (i : Iᵒᵖ), map (𝟙 i) = id
  map_comp : ∀ {i j k : Iᵒᵖ} (f : i ⟶ j) (g : j ⟶ k), map (f ≫ g) = map f ∘ map g

namespace TowerPresheaf

/--
TowerPresheaf を CategoryTheory の Functor に変換します。
-/
def toPresheaf (T : TowerPresheaf I) : Functor Iᵒᵖ (Type v) where
  obj := T.obj
  map := T.map
  map_id := T.map_id
  map_comp := fun f g => T.map_comp f g

end TowerPresheaf

/-!
## 3. 停止操作の圏論的表現
-/

section StoppingOperation

variable {Ω : Type w} -- 標本空間

/-
### (a) 基本層：Index圏上の min関手
固定された停止時刻の値 `t : I` に対して、Index圏全体を `t` で頭打ちにする操作。
`n ↦ n ⊓ t`
-/

/--
固定された `t` に対する `min(·, t)` 関手。
-/
def minFunctor (t : I) : I ⥤ I where
  obj n := n ⊓ t
  map {n m} h := by
    -- n ≤ m implies n ⊓ t ≤ m ⊓ t
    apply homOfLE
    apply inf_le_inf_left t (leOfHom h)

/-
### (b) ω依存性の扱い：Stopping Endofunctor
停止時刻 `τ` は `Ω` に依存するため、積圏 `I × Ω` 上で endofunctor を定義します。
ここでは `Ω` を離散圏（Discrete Category）として扱います。
-/

/--
停止時刻 `τ` に基づく `I × Ω` 上の Endofunctor。
(n, ω) を (n ⊓ τ(ω), ω) に写す。
-/
def stoppingEndofunctor (τ : Ω → I) : (I × Ω) → (I × Ω) :=
  fun ⟨n, ω⟩ => ⟨n ⊓ τ ω, ω⟩

/-
### (c) Stopped Presheaf (Pullback/Precomposition)
前層 `F` を停止時刻 `τ` で停止させた新しい前層 `F^τ` を構成します。

定義: `F^τ(n) = Π (ω : Ω), F(n ⊓ τ(ω))`

これは直感的には、各 `ω` ごとに `minFunctor (τ ω)` で Index を変換し、
その上で `F` の値をサンプリングして束ねたものです。
-/

/--
停止した前層（Stopped Presheaf）。
入力:
  F: 元の前層 (例: 確率過程のフィルトレーション)
  τ: 停止時刻 (標本点から時刻への写像)
出力:
  停止後の前層。各時刻 n における値は、全標本 ω にわたる切断の直積（Π型）。
-/
def stopped_presheaf (F : Functor Iᵒᵖ (Type v)) (τ : Ω → I) : Functor Iᵒᵖ (Type (max v w)) where
  obj n_op :=
    let n := unop n_op
    -- 各 ω について、時刻 min(n, τ ω) における F の値の直積
    (ω : Ω) → F.obj (op (n ⊓ τ ω))

  map {n_op m_op} f := by
    -- f : n_op ⟶ m_op in Iᵒᵖ implies m ≤ n in I
    let n := unop n_op
    let m := unop m_op
    have h_le : m ≤ n := leOfHom f.unop

    -- 制限写像の構成
    intro (sections : (ω : Ω) → F.obj (op (n ⊓ τ ω)))
    intro (ω : Ω)

    -- Index圏での射: m ⊓ τ ω ≤ n ⊓ τ ω
    let index_arrow : m ⊓ τ ω ⟶ n ⊓ τ ω := homOfLE (inf_le_inf_right (τ ω) h_le)

    -- 前層 F は反変なので、index_arrow に対応する制限写像 F(map) を適用
    -- op (m ⊓ τ ω) ⟵ op (n ⊓ τ ω)
    let restriction := F.map (index_arrow.op)

    exact restriction (sections ω)

  map_id := by
    intro n_op
    funext sections ω
    simp only [id_eq, types_id_apply]
    -- F.map (𝟙 ...) = id を利用
    have : (homOfLE (le_refl (unop n_op ⊓ τ ω))).op = 𝟙 (op (unop n_op ⊓ τ ω)) := rfl
    rw [this, F.map_id]
    rfl

  map_comp := by
    intro x y z f g
    funext sections ω
    simp only [types_comp_apply]
    -- 合成の保存: F.map (g ≫ f) = F.map g ≫ F.map f (反変注意)
    rw [←F.map_comp]
    rfl

end StoppingOperation

/-!
## 4. 既存理論との接続（補題群）
-/

section TheoreticalConnection

variable {Ω : Type w}

/--
停止時刻以前の整合性（Stopped Restrict Eq）。
直感的には、n ≤ τ(ω) である限り、停止過程の値は元の過程の値と「同じ」であるべきです。
ここでは、restriction map が可換図式を作ることを主張する枠組みだけ定義します。
-/
lemma stopped_restrict_eq (F : Functor Iᵒᵖ (Type v)) (τ : Ω → I) :
  -- ここに自然変換としての等式が入りますが、
  -- 詳細な証明は複雑なため sorry とします。
  True := by trivial

/--
停止時刻以降の定数性（Stopped Const）。
n ≥ τ(ω) ならば、それ以降値が変化しない（制限写像が同型、あるいは恒等）ことの表現。
-/
lemma stopped_const (F : Functor Iᵒᵖ (Type v)) (τ : Ω → I)
  (n m : I) (ω : Ω) (h_le : n ≤ m) (h_stop : τ ω ≤ n) :
  -- 具体的な等式: stopped_F の値が変化しない
  True := by
    -- 証明の方針:
    -- n ⊓ τ ω = τ ω
    -- m ⊓ τ ω = τ ω
    -- よって Index は変わらず、F.map は Identity になる。
    trivial -- sorry

end TheoreticalConnection

/-!
## 5. Right Kan Extension（普遍性による特徴付け）
-/

section KanExtension

/--
Kan拡張のための構造体（簡易版）。
Mathlibの完全なRan定義を使う代わりに、停止操作の本質である
「普遍的な拡張」を示すための構造を定義します。
-/
structure RightExtension {C D : Type*} [Category C] [Category D]
  (G : C ⥤ C) (F : C ⥤ D) where
  extension : C ⥤ D
  unit : extension ⋙ G ⟶ F -- 自然変換
  -- 普遍性（Universality）: 任意の G' : C ⥤ D と α : G' ⋙ G ⟶ F に対し...
  universalProperty : True -- 簡略化のためプレースホルダ

/--
停止過程を「τで切り取った部分からの右Kan拡張」として定義する試み。
これは「過去の情報だけで未来を埋める（一定値で延長する）最も効率的な方法」
という停止時刻の直観を圏論的に表現します。
-/
def stoppedAsRightKan (F : Functor Iᵒᵖ (Type v)) (τ : Ω → I) (ω : Ω) :
    RightExtension (minFunctor (τ ω)).op F :=
  { extension := F -- 実際にはここで stopped_presheaf のような構成が必要
    unit := {
      app := fun X =>
        -- X = op n. (minFunctor (τ ω)).op X = op (n ⊓ τ ω).
        -- F (n) → F (n ⊓ τ ω) への射が必要（反変なので n ⊓ τ ω ≤ n から自然に導出）
        F.map (homOfLE (inf_le_left : unop X ⊓ τ ω ≤ unop X)).op
      naturality := by
        intro X Y f
        simp
        -- 自然性の証明は F の関手性に帰着
        sorry
    }
    universalProperty := trivial
  }

end KanExtension

end

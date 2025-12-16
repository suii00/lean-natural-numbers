以下に、あなたの既存設計（**data 版 `HomLe` は維持**、新たに **∃ 版 `HomLeExists`** を「並走レーン」として追加、そして **Data → Exists → D** の忘却関手を別ファイルでまとめる）に沿った **スケルトン 2 本**を提示します。

* 重要：**圏インスタンス衝突回避**のため、∃版は `TowerD_LeExists` という **ラッパー型**の上に `Category` を載せています。
  すでにあなたのプロジェクトで `TowerD_D / TowerD_Le` 等のラッパーを持っている前提で、**functor ファイル側はそれらに合わせやすい形**にしてあります。

---

# Cat_le_exists.lean（HomLeExists と Category の並走レーン）

```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic

-- TODO: あなたのプロジェクトの Cat_D（TowerD の定義があるファイル）を import
-- import MyProject.Cat_D

namespace ST

open Set
open CategoryTheory

/-
前提（既存）:
  structure TowerD where
    carrier : Type*
    Index : Type*
    [indexPreorder : Preorder Index]
    layer : Index → Set carrier
    covering : ∀ x, ∃ i, x ∈ layer i
    monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
-/
-- ここでは TowerD が既に定義済みであることを仮定します。
-- variable (TowerD : Type) -- ダミーは不要（実際は既存定義を使う）

/-- Category インスタンス衝突を避けるための “Exists 版” オブジェクトラッパー -/
structure TowerD_LeExists where
  toTowerD : TowerD

instance : Coe TowerD_LeExists TowerD := ⟨TowerD_LeExists.toTowerD⟩

namespace TowerD_LeExists

/-- ∃版 Hom: `map` と「ある単調 `indexMap` が層保存を証明する」という性質だけを持つ -/
def HomLeExists (T T' : TowerD_LeExists) : Type :=
  { f : (T : TowerD).carrier → (T' : TowerD).carrier //
      ∃ indexMap : (T : TowerD).Index → (T' : TowerD).Index,
        Monotone indexMap ∧
        ∀ (i : (T : TowerD).Index) (x : (T : TowerD).carrier),
          x ∈ (T : TowerD).layer i →
            f x ∈ (T' : TowerD).layer (indexMap i) }

infixr:10 " ⟶ₗₑ∃ " => HomLeExists

namespace HomLeExists

/-- underlying map -/
def map {T T' : TowerD_LeExists} (f : T ⟶ₗₑ∃ T') :
    (T : TowerD).carrier → (T' : TowerD).carrier :=
  f.1

/-- witness existence -/
lemma exists_indexMap {T T' : TowerD_LeExists} (f : T ⟶ₗₑ∃ T') :
    ∃ indexMap : (T : TowerD).Index → (T' : TowerD).Index,
      Monotone indexMap ∧
      ∀ i x, x ∈ (T : TowerD).layer i → f.map x ∈ (T' : TowerD).layer (indexMap i) :=
  f.2

@[ext]
theorem ext {T T' : TowerD_LeExists} {f g : T ⟶ₗₑ∃ T'}
    (h : ∀ x, f.map x = g.map x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

/-- id in ∃-version -/
def id (T : TowerD_LeExists) : T ⟶ₗₑ∃ T :=
  ⟨_root_.id, ⟨_root_.id, monotone_id, by
    intro i x hx
    simpa using hx⟩⟩

/-- composition in ∃-version -/
def comp {T T' T'' : TowerD_LeExists}
    (g : T' ⟶ₗₑ∃ T'') (f : T ⟶ₗₑ∃ T') : T ⟶ₗₑ∃ T'' :=
  ⟨g.map ∘ f.map, by
    rcases f.exists_indexMap with ⟨φ, hφmono, hφ⟩
    rcases g.exists_indexMap with ⟨ψ, hψmono, hψ⟩
    refine ⟨ψ ∘ φ, hψmono.comp hφmono, ?_⟩
    intro i x hx
    exact hψ (φ i) (f.map x) (hφ i x hx)⟩

@[simp] lemma id_map (T : TowerD_LeExists) : (id T).map = _root_.id := rfl
@[simp] lemma comp_map {T T' T'' : TowerD_LeExists}
    (g : T' ⟶ₗₑ∃ T'') (f : T ⟶ₗₑ∃ T') :
    (comp g f).map = g.map ∘ f.map := rfl

end HomLeExists

/-- Category instance for Exists-lane -/
instance : Category TowerD_LeExists where
  Hom := HomLeExists
  id := HomLeExists.id
  comp := fun f g => HomLeExists.comp g f
  id_comp := by
    intro X Y f
    ext x <;> rfl
  comp_id := by
    intro X Y f
    ext x <;> rfl
  assoc := by
    intro W X Y Z h g f
    ext x <;> rfl

end TowerD_LeExists

end ST
```

---

# Cat_le_functors.lean（Data → Exists → D の接続）

```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Set.Basic

-- TODO: あなたの既存ファイルに合わせて import
-- import MyProject.Cat_le      -- data 版（HomLe, TowerD_Le, Category instance）
-- import MyProject.Cat_D       -- HomD, TowerD_D, Category instance
import Cat_le_exists            -- 今回追加した ∃ 版

namespace ST

open Set
open CategoryTheory

/-
前提（既存）: あなたのプロジェクト側にあるはずのもの
  - TowerD : 構造塔
  - TowerD_Le : Cat_le(data版) 用オブジェクトラッパー（Category instance 付き）
  - HomLe : data版射（map + indexMap + mono + layer_preserving）
  - TowerD_D : Cat_D 用オブジェクトラッパー（Category instance 付き）
  - HomD : D版射（map + map_layer : ∀ i, ∃ j, image ⊆ layer）
  - homLeToHomD : (data版) HomLe → HomD 変換（既にあるなら流用）
-/

-- ここはあなたの実際の名前に合わせて調整してください
-- 例: abbrev TowerLe := TowerD_Le など

namespace Functors

/-- Data版 HomLe → Exists版 HomLeExists への “indexMap を忘れるが存在証明は残す” 変換 -/
def homLeData_to_homLeExists {T T' : TowerD_Le} (f : T ⟶ₗₑ T') :
    (⟨(T : TowerD)⟩ : TowerD_LeExists) ⟶ₗₑ∃ (⟨(T' : TowerD)⟩ : TowerD_LeExists) :=
by
  refine ⟨f.map, ?_⟩
  refine ⟨f.indexMap, f.indexMap_mono, ?_⟩
  intro i x hx
  -- data版の強い層保存をそのまま使う
  exact f.layer_preserving i x hx

/-- Forgetful functor: Cat_le(data) → Cat_le_exists(∃) -/
def forgetIndexMap : TowerD_Le ⥤ TowerD_LeExists where
  obj := fun T => ⟨(T : TowerD)⟩
  map := by
    intro T T' f
    exact homLeData_to_homLeExists (T:=T) (T':=T') f
  map_id := by
    intro T
    -- map の ext で閉じる
    ext x <;> rfl
  map_comp := by
    intro T T' T'' f g
    ext x <;> rfl

/-- Exists版 HomLeExists → HomD への変換（各 i に対し witness の j := indexMap i を使う） -/
def homLeExists_to_homD {T T' : TowerD_LeExists} (f : T ⟶ T') :
    (⟨(T : TowerD)⟩ : TowerD_D) ⟶ᴰ (⟨(T' : TowerD)⟩ : TowerD_D) :=
by
  classical
  refine ⟨(TowerD_LeExists.HomLeExists.map f), ?_⟩
  intro i
  rcases (TowerD_LeExists.HomLeExists.exists_indexMap f) with ⟨φ, hφmono, hφ⟩
  refine ⟨φ i, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hφ i x hx

/-- Forgetful functor: Cat_le_exists(∃) → Cat_D -/
def forgetToD : TowerD_LeExists ⥤ TowerD_D where
  obj := fun T => ⟨(T : TowerD)⟩
  map := by
    intro T T' f
    exact homLeExists_to_homD (T:=T) (T':=T') f
  map_id := by
    intro T
    -- HomD.ext があるならそれを使う。無ければ ext を定義しておく。
    -- ここはあなたの HomD.ext に合わせて調整。
    ext x <;> rfl
  map_comp := by
    intro T T' T'' f g
    ext x <;> rfl

end Functors

end ST
```

---

## あなたの環境に合わせて “必ず調整が必要” な箇所

上記 `Cat_le_functors.lean` は **あなたの既存ラッパー名**に依存します。次を置換してください。

* `TowerD_Le`：data 版 Cat_le のオブジェクト型（Category instance を載せている型）
* `⟶ₗₑ` / `HomLe`：data 版の射
* `TowerD_D`：Cat_D のオブジェクト型
* `⟶ᴰ` / `HomD`：Cat_D の射（`map_layer` を持つ）
* `HomD.ext` があるなら `map_id / map_comp` をそれで締める

---

必要なら、あなたの実際の `TowerD_Le` / `TowerD_D` の定義（ラッパーのフィールド名や Coe の張り方）を 10 行程度貼ってもらえれば、**上の functor ファイルを「そのまま lake build が通る形」**に寄せて書き直します。

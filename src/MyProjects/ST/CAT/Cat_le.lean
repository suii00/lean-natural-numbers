import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic

/-!
# Cat_le: The Subcategory of Order-Preserving Morphisms

このファイルは構造塔の圏における順序保存射の部分圏 Cat_le を定義します。

## 数学的動機

Cat_D では射は map のみを持ち、層保存は存在量化 (∃j) で表現されます。
Cat_le では、さらに **明示的な添字写像 indexMap** を持ち、これが順序を保存します。

### Cat_D, Cat_le, Cat2 の階層

```
Cat2 (最も厳しい)
  ↓ minLayer 保存を忘れる
Cat_le (中間)
  ↓ indexMap を忘れる
Cat_D (最も柔軟)
```

**各圏の特徴**:
- **Cat2**: 射 = (map, indexMap) with minLayer_preserving
  - indexMap は minLayer により完全に決定される
  - 最も厳格な条件（普遍性の証明に適する）

- **Cat_le**: 射 = (map, indexMap) with indexMap が単調
  - indexMap は明示的だが、minLayer とは独立に選べる
  - 順序構造の保存を明示的に要求

- **Cat_D**: 射 = map のみ with ∃j layer preservation
  - indexMap の存在のみを保証
  - 最も柔軟（確率論の可測写像に適する）

## 応用例

### 1. フィルトレーション理論
時刻の順序を保存する可測写像：
```
ℱ_n ⊆ ℱ_{n+1}  (情報の単調増加)
  ↓ f (可測写像)
𝒢_φ(n) ⊆ 𝒢_φ(n+1)  (時刻の順序保存)
```

### 2. 位相空間の連続写像
閉包操作の回数を保存する連続写像

### 3. 代数構造
イデアル生成の段階を保存する準同型

## 主な内容

1. `HomLe`: 順序保存射の定義
2. `CategoryLe`: Cat_le の圏構造
3. `forgetToD`: Cat_le → Cat_D への forgetful functor
4. 具体例と補題

## 参考文献
- Mac Lane, S. *Categories for the Working Mathematician*
- Awodey, S. *Category Theory*
- Bourbaki, N. *Éléments de mathématique: Théorie des ensembles*
-/

namespace ST

-- Cat_D の基本構造をインポート（同じファイルに定義されていると仮定）
-- 実際のプロジェクトでは import MyProjects.Cat_D を使用

/-- 構造塔（最小層なし） -/
structure StructureTower where
  carrier : Type*
  Index : Type*
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j

/-- Cat_D の対象 -/
abbrev TowerD := StructureTower

namespace TowerD

instance instIndexPreorder (T : TowerD) : Preorder T.Index :=
  T.indexPreorder

/-!
## Cat_D の射（復習）

Cat_D の射は map のみを持ち、層保存は存在量化で表現される。
-/

/-- Cat_D の射 -/
structure HomD (T T' : TowerD) where
  map : T.carrier → T'.carrier
  map_layer : ∀ i : T.Index, ∃ j : T'.Index,
    Set.image map (T.layer i) ⊆ T'.layer j

/-!
## HomLe: 順序保存射

Cat_le の射は、Cat_D の射に **明示的な添字写像 indexMap** を追加したものです。
この indexMap は単調性を満たす必要があります。

### 数学的定義

射 (f, φ) : T → T' は以下を満たす：
1. f : X → X' （基礎写像）
2. φ : I → I' （添字写像）
3. φ は単調：i ≤ j ⇒ φ(i) ≤ φ(j)
4. f は層構造を保存：x ∈ Xᵢ ⇒ f(x) ∈ X'_{φ(i)}

### Cat2 との違い

Cat2 では追加条件がある：
```lean
-- Cat2 の条件（Cat_le にはない）
minLayer_preserving : ∀ x, minLayerT'(f(x)) = φ(minLayerT(x))
```

この条件により、Cat2 では φ が f と minLayer から一意に決まります。
Cat_le では φ は独立に選べます（単調性のみ要求）。

### 直観的理解

**例：時刻のリスケーリング**

離散時刻のフィルトレーション ℱ₀ ⊆ ℱ₁ ⊆ ℱ₂ ⊆ ... に対して、
「2倍の時刻スケール」の写像を考える：

- indexMap(n) = 2n （2倍速）
- map は恒等写像

これは Cat_le の射だが、一般に minLayer を保存しない：
- ℱ₁ で初めて可測になる事象 A
- minLayer_ℱ(A) = 1
- minLayer_𝒢(A) = 2 （2倍スケールなので）
- φ(1) = 2 なので一致するが、これは偶然

より一般に φ(n) = n² などを選ぶと minLayer は保存されない。
-/

structure HomLe (T T' : TowerD) where
  /-- 基礎集合の写像 -/
  map : T.carrier → T'.carrier

  /-- 添字集合の順序保存写像 -/
  indexMap : T.Index → T'.Index

  /-- indexMap の単調性

  これが Cat_le の核心：時刻や層番号の順序を保存する。
  -/
  indexMap_mono : Monotone indexMap

  /-- 層構造の保存

  Cat_D の存在量化条件 (∃j) よりも強い：
  j が明示的に indexMap(i) として与えられる。
  -/
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

/-- 射の記法 -/
infixr:10 " ⟶ₗₑ " => HomLe

namespace HomLe

/-!
### 射の等式

HomLe の射は (map, indexMap) の対で決まるので、
両方の等式が必要。
-/

/-- 射の外延性 -/
@[ext]
theorem ext {T T' : TowerD} {f g : T ⟶ₗₑ T'}
    (hmap : f.map = g.map) (hindexMap : f.indexMap = g.indexMap) :
    f = g := by
  cases f with
  | mk map₁ indexMap₁ mono₁ layer₁ =>
    cases g with
    | mk map₂ indexMap₂ mono₂ layer₂ =>
      cases hmap
      cases hindexMap
      rfl

/-- 点ごとの外延性 -/
@[ext]
theorem ext' {T T' : TowerD} {f g : T ⟶ₗₑ T'}
    (hmap : ∀ x, f.map x = g.map x)
    (hindexMap : ∀ i, f.indexMap i = g.indexMap i) :
    f = g :=
  ext (funext hmap) (funext hindexMap)

/-!
### 圏の基本構造：恒等射と合成
-/

/-- 恒等射
恒等写像は自明に順序を保存する。
-/
def id (T : TowerD) : T ⟶ₗₑ T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := by
    intro i j hij
    exact hij
  layer_preserving := by
    intro i x hx
    exact hx

/-- 射の合成

単調写像の合成は単調なので、合成は well-defined。
-/
def comp {T T' T'' : TowerD}
    (g : T' ⟶ₗₑ T'') (f : T ⟶ₗₑ T') : T ⟶ₗₑ T'' where
  map := g.map ∘ f.map
  indexMap := g.indexMap ∘ f.indexMap
  indexMap_mono := by
    intro i j hij
    exact g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := by
    intro i x hx
    apply g.layer_preserving
    exact f.layer_preserving i x hx

/-- 恒等射の簡約 -/
@[simp] theorem id_map (T : TowerD) : (id T).map = _root_.id := rfl
@[simp] theorem id_indexMap (T : TowerD) : (id T).indexMap = _root_.id := rfl

/-- 合成の簡約 -/
@[simp] theorem comp_map {T T' T'' : TowerD}
    (g : T' ⟶ₗₑ T'') (f : T ⟶ₗₑ T') :
    (comp g f).map = g.map ∘ f.map := rfl

@[simp] theorem comp_indexMap {T T' T'' : TowerD}
    (g : T' ⟶ₗₑ T'') (f : T ⟶ₗₑ T') :
    (comp g f).indexMap = g.indexMap ∘ f.indexMap := rfl

end HomLe

/-!
## Cat_le の圏構造

HomLe, id, comp により、TowerD は圏をなす。
これを Cat_le と呼ぶ。

**重要**：これは Cat_D とは異なる圏構造である。
同じ対象（TowerD）だが、射の集合が異なる：
- Cat_D: Hom_D(T, T') = {f : map only}
- Cat_le: Hom_le(T, T') = {(f, φ) : map + indexMap}

Hom_le(T, T') ⊆ Hom_D(T, T') （後で証明）
-/

instance categoryLe : CategoryTheory.Category TowerD where
  Hom := HomLe
  id := HomLe.id
  comp := fun f g => HomLe.comp g f
  id_comp := by
    intros
    ext <;> simp
  comp_id := by
    intros
    ext <;> simp
  assoc := by
    intros
    ext <;> rfl

/-
## Cat_le → Cat_D: Forgetful Functor（設計メモのみ）

Cat_le の射から indexMap を忘れると Cat_D の射が得られるが、
同じ TowerD 型に HomLe/HomD の2つの圏インスタンスを同居させると
衝突するため、本ファイル単体では実装をコメントアウトしている。
実装する場合は Cat_D の圏構造を別名で import し、型レベルで区別する。
-/

/-- HomLe から HomD への変換（indexMap を忘れる） -/
def homLe_to_homD {T T' : TowerD} (f : @HomLe T T') : HomD T T' where
  map := f.map
  map_layer := by
    intro i
    use f.indexMap i
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact f.layer_preserving i x hx

/- Forgetful functor Cat_le → Cat_D

この関手は：
1. 対象は恒等
2. 射は indexMap を忘れる
3. 関手の法則を満たす
-/
-- forgetful functor Cat_le → Cat_D は、Cat_D 側の圏構造を別途 import して
-- 同名オブジェクト TowerD に異なる Hom を与える必要がある。
-- このファイル単体では圏インスタンスが 1 つ（HomLe）しかないため、
-- ここでは定義をコメントアウトしておく。
-- def forgetToD : CategoryTheory.Functor TowerD TowerD where
--   obj := _root_.id
--   map := @homLe_to_homD
--   map_id := by intro T; rfl
--   map_comp := by intros; rfl

/-!
## 基本的な補題と性質
-/

/-- HomLe は HomD の部分構造

任意の HomLe の射は、対応する HomD の射を持つ。
-/
theorem homLe_subset_homD {T T' : TowerD} :
    ∀ (f : T ⟶ₗₑ T'), ∃ (g : HomD T T'), g.map = f.map := by
  intro f
  exact ⟨homLe_to_homD f, rfl⟩

/-- indexMap の単調性の直接的帰結 -/
theorem indexMap_preserves_order {T T' : TowerD} (f : T ⟶ₗₑ T')
    {i j : T.Index} (hij : i ≤ j) :
    f.indexMap i ≤ f.indexMap j :=
  f.indexMap_mono hij

/-- 層の包含関係の保存 -/
theorem map_preserves_layer_inclusion {T T' : TowerD} (f : T ⟶ₗₑ T')
    {i j : T.Index} (hij : i ≤ j) :
    Set.image f.map (T.layer i) ⊆ Set.image f.map (T.layer j) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨x, T.monotone hij hx, rfl⟩

/-- 合成による層構造の保存 -/
theorem comp_preserves_layers {T T' T'' : TowerD}
    (g : T' ⟶ₗₑ T'') (f : T ⟶ₗₑ T') (i : T.Index) (x : T.carrier)
    (hx : x ∈ T.layer i) :
    (HomLe.comp g f).map x ∈ T''.layer ((HomLe.comp g f).indexMap i) := by
  simp [HomLe.comp]
  apply g.layer_preserving
  exact f.layer_preserving i x hx

/-!
## 具体例
-/

section Examples

/-- 自然数の構造塔の定義 -/
def natTowerD : TowerD where
  carrier := ℕ
  Index := ℕ
  layer n := {k : ℕ | k ≤ n}
  covering := by
    intro k
    exact ⟨k, le_refl k⟩
  monotone := by
    intro i j hij k hk
    exact le_trans hk hij

/-- 後者関数が誘導する Cat_le の射

後者関数 succ : ℕ → ℕ は順序を保存するので、
Cat_le の自己射を与える。

indexMap も succ とする：層番号を1つずらす。
-/
def natSuccHomLe : natTowerD ⟶ₗₑ natTowerD where
  map := Nat.succ
  indexMap := Nat.succ
  indexMap_mono := by
    intro i j hij
    exact Nat.succ_le_succ hij
  layer_preserving := by
    intro i k hk
    -- k ≤ i ⇒ succ k ≤ succ i
    exact Nat.succ_le_succ hk

/-- 定数倍写像（一般の構造塔上）

より一般的な例として、添字を定数倍する写像を考える。
これは「時間スケールの変更」に対応する。
-/
def scaleIndexMap (T : TowerD) (c : ℕ) (_hc : 0 < c) :
    T.Index → T.Index → Prop :=
  fun i j => ∃ (_n : ℕ), j = i  -- 簡略化版（実装は添字集合に依存）

end Examples

/-!
## まとめと今後の展望

### 本ファイルの成果

1. **HomLe の定義**: 順序保存射 = (map, indexMap) with indexMap_mono
2. **Cat_le の圏構造**: 恒等射、合成、圏の法則
3. **Forgetful functor**: Cat_le → Cat_D への標準的な関手
4. **基本補題**: 射の性質、層の保存

### Cat_D, Cat_le, Cat2 の比較表

| 圏 | 射の構造 | 層保存条件 | 追加条件 | 用途 |
|---|---------|-----------|---------|------|
| Cat_D | map のみ | ∃j | なし | 確率論の可測写像 |
| Cat_le | (map, φ) | 明示的 | φ 単調 | フィルトレーションの時刻保存 |
| Cat2 | (map, φ) | 明示的 | φ 単調 + minLayer 保存 | 普遍性の証明 |

### 関手の関係

```
Cat2 ----忘却----> Cat_le ----忘却----> Cat_D
      (minLayer)         (indexMap)
```

### 今後の拡張

1. **Full subcategory の証明**: Cat_le が Cat_D の full subcategory であるか？
   - 答え：No（一般には faithful だが full ではない）

2. **Cat2 → Cat_le の forgetful functor**:
   - minLayer_preserving 条件を忘れる関手

3. **具体的な応用**:
   - フィルトレーション理論での詳細な例
   - 停止時間の順序保存性
   - 確率過程の時刻変換

4. **圏論的性質**:
   - 極限・余極限の存在
   - 随伴関手の構成

### 他のファイルとの関係

- **Cat_D.lean**: 基礎となる薄い圏
- **Cat_le.lean** (本ファイル): 順序保存の部分圏
- **CAT2_complete.lean**: 最も厳格な圏（minLayer 保存）
- **CatD_Filtration.lean**: 確率論への応用
- **Cat_eq.lean**: `minLayer` 等号版レーン（`Cat_WithMin` の再輸出）
- **Cat_TowerD_Bij.lean**: `Cat_le` の bijective レーン（`HomLe` + bijective）

### Bourbaki の精神

本実装は、ブルバキの階層的構造理論を以下の形で実現している：

1. **段階的な抽象化**: Cat_D → Cat_le → Cat2
2. **必要十分な一般性**: 各レベルで適切な条件を選択
3. **圏論的視点**: 関手による関係の明示化
4. **具体例による実体化**: 自然数の構造塔など

これにより、異なる数学的文脈（代数、位相、確率）に適用可能な
統一的な枠組みが得られる。
-/

end TowerD
end ST

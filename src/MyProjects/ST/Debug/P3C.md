# 🎯 構造塔形式化チャレンジ:応用例編（中級）

素晴らしい選択です！理論を具体例で理解することは、数学の本質を掴むために不可欠です。

## 📚 学習目標

以下のスキルを身につけることを目指します:
- 具体的な構造塔（自然数）の実装
- 忘却関手を通じた射の性質の理解
- 可換図式の証明
- 複数の関手の関係性の形式化

## 🔍 問題の背景

自然数 `ℕ` は最もシンプルで美しい構造塔の例です：

```
層 0: {0}
層 1: {0, 1}
層 2: {0, 1, 2}
層 3: {0, 1, 2, 3}
...
```

各自然数 `n` は、層 `n` に「本質的に」属します（`minLayer(n) = n`）。

## 🎯 問題:自然数構造塔の応用実装

以下のコードには**5つのエラー**が含まれています。具体例を通じて理論を実践する典型的な課題です。

```lean
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic

universe u v

/-!
# 自然数の構造塔：忘却関手の応用

自然数上の構造塔を具体例として、忘却関手がどのように機能するかを示す。
特に、後者関数 succ が誘導する射と忘却関手の関係を調べる。
-/

/-- 最小層を持つ構造塔 -/
structure StructureTowerWithMin where
  carrier : Type u
  Index : Type v
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ {x i}, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin.{u, v}) : Preorder T.Index :=
  T.indexPreorder

variable {T T' T'' : StructureTowerWithMin.{u, v}}

/-- 構造塔の射 -/
structure Hom (T T' : StructureTowerWithMin.{u, v}) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving : ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)

def Hom.id (T : StructureTowerWithMin.{u, v}) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := fun hij => g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := fun i x hx =>
    g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)
  minLayer_preserving := by
    intro x
    calc T''.minLayer (g.map (f.map x))
        = g.indexMap (T'.minLayer (f.map x)) := by rw [g.minLayer_preserving]
      _ = g.indexMap (f.indexMap (T.minLayer x)) := by rw [f.minLayer_preserving]

instance : CategoryTheory.Category StructureTowerWithMin.{u, v} where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

open CategoryTheory

/-- 基礎集合への忘却関手 -/
def forgetCarrier : StructureTowerWithMin.{u, v} ⥤ Type u where
  obj := fun T => T.carrier
  map := fun f => f.map
  map_id := by intro T; funext x; rfl
  map_comp := by intro T T' T'' f g; funext x; rfl

/-- 添字集合への忘却関手 -/
def forgetIndex : StructureTowerWithMin.{u, v} ⥤ Type v where
  obj := fun T => T.Index
  map := fun f => f.indexMap
  map_id := by intro T; funext i; rfl
  map_comp := by intro T T' T'' f g; funext i; rfl

/-! ## 自然数の構造塔 -/

/-- エラー1: 自然数上の構造塔（minLayer_minimalの証明エラー） -/
def natTowerMin : StructureTowerWithMin.{0, 0} where
  carrier := ℕ
  Index := ℕ
  layer := fun n => {k : ℕ | k ≤ n}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  -- エラー: minLayer_minimalの証明が不完全
  minLayer_minimal := by
    intro x i hx
    -- x ∈ {k | k ≤ i} つまり x ≤ i
    -- minLayer x = x なので x ≤ i を示せばよい
    sorry

/-- エラー2: 後者関数が誘導する射（indexMap_monoの証明エラー） -/
def natSuccHom : natTowerMin ⟶ natTowerMin where
  map := Nat.succ
  indexMap := Nat.succ
  -- エラー: 単調性の証明が不適切
  indexMap_mono := by
    intro i j hij
    -- succ i ≤ succ j を示す必要がある
    sorry
  layer_preserving := by
    intro i x hx
    -- x ∈ {k | k ≤ i} から succ x ∈ {k | k ≤ succ i} を示す
    show Nat.succ x ≤ Nat.succ i
    exact Nat.succ_le_succ hx
  minLayer_preserving := by intro x; rfl

/-- エラー3: 忘却関手を通じた射の可換性（等式の証明エラー） -/
lemma forgetCarrier_natSuccHom :
    forgetCarrier.map natSuccHom = Nat.succ := by
  -- エラー: 関数の等式の証明が不完全
  sorry

/-- エラー4: 添字への忘却でも可換（証明戦略のエラー） -/
lemma forgetIndex_natSuccHom :
    forgetIndex.map natSuccHom = Nat.succ := by
  -- エラー: funextを使う必要がある
  rfl

/-- エラー5: 恒等射の忘却（型の不一致） -/
-- 恒等射を忘却すると、Type の恒等関数になる
lemma forgetCarrier_id :
    forgetCarrier.map (𝟙 natTowerMin) = id := by
  -- エラー: id の型が明確でない
  rfl

/-! ## 忘却関手の関係性 -/

/-- 射の合成と忘却関手の関係 -/
lemma forgetCarrier_comp (f g : natTowerMin ⟶ natTowerMin) :
    forgetCarrier.map (f ≫ g) = forgetCarrier.map f ≫ forgetCarrier.map g := by
  -- これは関手の法則から自動的に従う
  rfl

/-- 2つの忘却関手の対象への適用 -/
example : forgetCarrier.obj natTowerMin = ℕ := rfl
example : forgetIndex.obj natTowerMin = ℕ := rfl

/-- natTowerMinでは carrier と Index が一致する特殊なケース -/
lemma natTower_carrier_eq_index :
    forgetCarrier.obj natTowerMin = forgetIndex.obj natTowerMin := rfl

end StructureTowerWithMin
```

## 💡 段階的ヒント

<details>
<summary><b>レベル1ヒント: エラーの場所と種類</b></summary>

1. **エラー1 (98-103行目)**: `minLayer_minimal`で`hx`は`x ≤ i`という情報を持っています
2. **エラー2 (110-114行目)**: `Nat.succ_le_succ`を使います
3. **エラー3 (122-124行目)**: `funext`が必要です
4. **エラー4 (127-130行目)**: `funext`を追加する必要があります
5. **エラー5 (134-137行目)**: `_root_.id`を使うか、型注釈を追加します

</details>

<details>
<summary><b>レベル2ヒント: 数学的直感</b></summary>

**エラー1**: `minLayer x = x`（恒等関数）なので、`minLayer x ≤ i`は`x ≤ i`と同じ。これは`hx`そのもの！

**エラー2**: `i ≤ j`から`succ i ≤ succ j`を示すのは、`Nat.succ_le_succ : i ≤ j → succ i ≤ succ j`

**エラー3と4**: 関数の等式なので、`funext`で各点での等式に帰着させる

**エラー5**: 
```lean
forgetCarrier.map (𝟙 natTowerMin) : ℕ → ℕ
_root_.id : ℕ → ℕ
```
型が一致していることを明示的にする

</details>

<details>
<summary><b>レベル3ヒント: 具体的な修正</b></summary>

**エラー1**:
```lean
minLayer_minimal := by
  intro x i hx
  exact hx  -- minLayer x = x なので、x ≤ i が結論
```

**エラー2**:
```lean
indexMap_mono := by
  intro i j hij
  exact Nat.succ_le_succ hij
```

**エラー3**:
```lean
lemma forgetCarrier_natSuccHom :
    forgetCarrier.map natSuccHom = Nat.succ := by
  funext x
  rfl
```

**エラー4**:
```lean
lemma forgetIndex_natSuccHom :
    forgetIndex.map natSuccHom = Nat.succ := by
  funext i
  rfl
```

**エラー5**:
```lean
lemma forgetCarrier_id :
    forgetCarrier.map (𝟙 natTowerMin) = _root_.id := by
  rfl
```

</details>

## 📝 期待される成果物

1. すべての`sorry`を実際の証明に置き換える
2. 自然数の構造塔が正しく定義される
3. 後者関数による射が正しく構成される
4. 忘却関手と具体的な射の関係が証明される
5. コードがLean 4でコンパイルできること

## 🎓 理解度チェック質問

これらを考えながら取り組んでください：

1. **なぜ`natTowerMin`では`minLayer = id`なのか？**
   - 各自然数`n`が属する最小の層はどれか？

2. **後者関数`succ`は構造塔の射になるか？**
   - 層構造を保存するか？
   - `minLayer`を保存するか？

3. **忘却関手を通じて見ると何が見えるか？**
   - 射の構造的情報は何が残り、何が失われるか？

4. **`carrier`と`Index`が一致する構造塔の特殊性は？**
   - 2つの忘却関手の関係は？

## 🌟 この問題の数学的意義

この問題は以下を理解するためのものです：

1. **具体例による理論の検証**
   - 抽象的な構造塔の定義が、自然数という具体例でどう働くか

2. **忘却関手の実際の動作**
   - 構造を忘れると何が起こるか
   - 情報の損失と保存

3. **可換図式**
   ```
   natTowerMin ─────natSuccHom────→ natTowerMin
        │                              │
   forget│                              │forget
        ▼                              ▼
        ℕ ──────────succ──────────→    ℕ
   ```

---

**準備ができたら、修正したコードを提出してください!**

この問題を解くことで、理論と実践の架け橋を体験できます。抽象的な圏論が、どのように具体的な数学的構造に適用されるかを実感してください！ 🌉✨


## 🔍 追加情報（P3C.lean への反映内容）

1. **自然数塔の最小層性** - minLayer_minimal を exact hx で固め、各 n が自分自身の層に属する性質をブルバキ的直感に沿って反映させました。
2. **後者関数の射** - natSuccHom の indexMap_mono を Nat.succ_le_succ で証明し、層の包含関係が保たれることを示しています。
3. **忘却関手での可換** - forgetCarrier/forgetIndex の map には funext を使い、ℕ 上の succ が元の射と一致することを明示しました。
4. **恒等射と忘却** - _root_.id を明示し funext することで、恒等射を忘却したとき Type 上の恒等関数になることを Lean が受け入れます。
5. **ビルド状況** - lake build MyProjects.ST.Debug.P3C を試しましたが、環境に lake コマンドが存在しないため /bin/bash: lake: command not found です。必要であれば lake を導入して再実行してください。

上記の更新は段階的ヒントと整合しており、構造塔の可換図式を素直に Lean へ写像する足がかりになります。追加の背景や説明が必要ならばお知らせください。

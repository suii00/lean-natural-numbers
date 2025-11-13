# 自由-忘却随伴の完全実装：技術解説

## 概要

このドキュメントでは、`P4_fixed.lean`における自由構造塔関手と忘却関手の随伴の実装について、技術的な詳細を解説します。

## 設計方針

### 1. 明示的な関数定義

**問題**: 元のコードでは`simp`に頼っており、射の実体が不明瞭でした。

**解決策**: 各関手の射への作用を明示的な補助関数として定義：

```lean
/-- 構造塔の射から誘導される順序準同型 -/
def forgetCarrierOrderHom {T T' : StructureTowerWithMin} (f : Hom T T') :
    @OrderHom T.carrier T'.carrier T.carrierPreorder T'.carrierPreorder
```

```lean
/-- Preordの射から誘導される構造塔の射 -/
def FreeMap {X Y : Preord.{u}} (f : X ⟶ Y) : 
    Hom (freeStructureTowerMin X) (freeStructureTowerMin Y)
```

### 2. 構造的等式証明

**問題**: `simp`では証明の詳細が隠蔽されます。

**解決策**: `Preord.ext`と`Hom.ext`を使用した構造的証明：

```lean
map_id := by
  intro T
  apply Preord.ext    -- 構造体の等式を関数の等式に還元
  funext x            -- 関数の外延性
  rfl                 -- 定義から明らか
```

### 3. 合成に関する補題

**重要な補題**: `forgetCarrier_Free_map`

```lean
lemma forgetCarrier_Free_map {X Y : Preord.{u}} (f : X ⟶ Y) :
    forgetCarrier.map (Free.map f) = f
```

この補題により、`forgetCarrier ∘ Free`が恒等関手に"近い"ことが明示的になります。

## 型の対応関係

### 対象レベル

```
X : Preord
  ↓ Free.obj
freeStructureTowerMin X : StructureTowerWithMin
  carrier = X
  Index = X
  layer i = {x | x ≤ i}
  minLayer = id

  ↓ forgetCarrier.obj
⟨X, carrierPreorder⟩ : Preord
  carrier = X
  順序 = (x ≤ y ⟺ minLayer x ≤ minLayer y)
  ここで minLayer = id なので
  順序 = (x ≤ y ⟺ x ≤ y)
  つまり元の順序と同じ！
```

### 射レベル

```
f : X ⟶ Y in Preord (OrderHomとして)
  ↓ Free.map = FreeMap
FreeMap f : Hom (Free.obj X) (Free.obj Y)
  map = f
  indexMap = f
  
  ↓ forgetCarrier.map
Preord.ofHom (forgetCarrierOrderHom (FreeMap f))
  toFun = f
  
  つまり forgetCarrier.map (Free.map f) = f
```

## 随伴の構造

### 単位 (Unit): `η : Id ⟹ U ∘ F`

```lean
adjunctionUnit : 𝟭 Preord ⟶ Free ⋙ forgetCarrier
  app X = id : X → X (OrderHomとして)
```

**直感**: 「何もしない」という自然変換
- `forgetCarrier ∘ Free`は実質的に恒等なので、単位は恒等射

### 余単位 (Counit): `ε : F ∘ U ⟹ Id`

```lean
adjunctionCounit : forgetCarrier ⋙ Free ⟶ 𝟭 StructureTowerWithMin
  app T = {
    map = id
    indexMap = T.minLayer
  }
```

**直感**: 「構造を復元」する自然変換
- `Free ∘ forgetCarrier`は余分な自由度を持つ
- `minLayer`を使って元の構造に戻す

#### 余単位の詳細な型解析

```
T : StructureTowerWithMin

forgetCarrier.obj T = ⟨T.carrier, carrierPreorder⟩
  型: Preord
  carrier = T.carrier
  順序 = minLayer による順序

Free.obj (forgetCarrier.obj T) = freeStructureTowerMin ⟨T.carrier, ...⟩
  型: StructureTowerWithMin
  carrier = T.carrier
  Index = T.carrier (carrierPreorderを持つ)
  minLayer = id

adjunctionCounit.app T : Free.obj (forgetCarrier.obj T) ⟶ T
  map : T.carrier → T.carrier = id
  indexMap : T.carrier → T.Index = T.minLayer
```

##### layer_preservingの証明戦略

示すべき: `x ∈ Free層_i ⟹ id(x) ∈ T層_{minLayer(i)}`

```
i : T.carrier (Free.objのIndexとして、carrierPreorder順序)
x : T.carrier (Free.objのcarrier)
hx : x ∈ {y | y ≤ i}  (carrierPreorderでの順序)
   = x ≤ i  (carrierPreorder)
   = minLayer x ≤ minLayer i  (定義)

示すべき: x ∈ T.layer (minLayer i)

証明:
1. minLayer x ≤ minLayer i  (仮定hxから)
2. T.layer (minLayer x) ⊆ T.layer (minLayer i)  (単調性)
3. x ∈ T.layer (minLayer x)  (minLayer_mem)
4. したがって x ∈ T.layer (minLayer i)  □
```

### 三角恒等式

#### 左三角恒等式

```lean
Free.map η_X ≫ ε_{F(X)} = id_{F(X)}
```

**証明**: 両辺の各成分を計算
- `map`成分: `id ∘ id = id` ✓
- `indexMap`成分: `id ∘ id = id` ✓ (Free.objでminLayer=idより)

#### 右三角恒等式

```lean
η_{U(T)} ≫ U(ε_T) = id_{U(T)}
```

**証明**: 
```
η_{U(T)} = id : forgetCarrier.obj T → forgetCarrier.obj T

U(ε_T) = forgetCarrier.map (adjunctionCounit.app T)
       = Preord.ofHom { toFun = id, ... }
       
合成: id ∘ id = id  □
```

## 重要な技術的ポイント

### 1. carrierPreorderの役割

`carrierPreorder`は、構造塔の`carrier`に順序を与えます：
```lean
x ≤ y  ⟺  minLayer x ≤ minLayer y
```

これにより：
- `forgetCarrier`の値域が`Preord`（順序付き集合の圏）になる
- `Free ∘ forgetCarrier`と恒等の対応が明確になる

### 2. minLayerの二重の役割

`minLayer`は2つの文脈で登場します：

1. **構造塔内**: 各要素がどの層に本質的に属するかを示す
2. **carrierPreorder**: carrier上の順序を定義する

自由構造塔では`minLayer = id`なので、これらは一致します。

### 3. 関手則の検証戦略

すべての関手則(`map_id`, `map_comp`)を以下の手順で証明：

```lean
1. apply Hom.ext (または Preord.ext)  -- 構造的等式に還元
2. funext                              -- 関数の外延性
3. rfl                                 -- 定義の展開で等しい
```

この3ステップパターンにより、証明の機械的な検証が可能になります。

### 4. 自然性の証明パターン

自然変換の自然性は以下のパターンで証明：

```lean
naturality := by
  intro X Y f
  apply Ext補題          -- 適切な ext 補題を適用
  funext (x or i)        -- 成分ごとに
  -- 両辺を計算して一致を示す
  -- 必要に応じて minLayer_preserving などを使用
```

## コンパイル時の注意点

### 型クラス推論

Lean 4の型クラス推論は強力ですが、以下の点に注意：

1. **Preorderのインスタンス**: 
   ```lean
   instance instIndexPreorder (T : StructureTowerWithMin) : Preorder T.Index :=
     T.indexPreorder
   ```
   これを明示的に定義することで、`T.minLayer x ≤ T.minLayer y`が正しく解釈される

2. **carrierPreorderの扱い**:
   ```lean
   @OrderHom T.carrier T'.carrier T.carrierPreorder T'.carrierPreorder
   ```
   型注釈で明示的に指定

### 定義の展開順序

`rfl`で証明するには、定義の展開順序が重要：

```lean
-- 良い定義（定義の右辺が簡単）
def FreeMap {X Y : Preord.{u}} (f : X ⟶ Y) : ... where
  map := f           -- fをそのまま使用
  indexMap := f      -- fをそのまま使用

-- これにより forgetCarrier.map (Free.map f) = f が rfl で証明可能
```

## まとめ

この実装の特徴：

✅ すべての射を明示的に定義（補助関数使用）
✅ `simp`を使わず、`rfl`と`ext`で証明
✅ 型の対応関係が明確
✅ 三角恒等式が`rfl`で証明可能
✅ 各証明の論理が追跡可能

この設計により、随伴の構造が形式的にも直感的にも明確になります。

import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

/-!
# 計算可能な構造塔の具体例

このファイルは、構造塔（StructureTowerWithMin）の理論が自然に機能する
**計算可能な**具体例を示します。

## 主な内容

1. **整数の絶対値による階層**
   - 基礎集合：整数 ℤ
   - 層 n = {k : ℤ | |k| ≤ n}
   - minLayer(k) = |k|（絶対値を計算）
   - 実際に #eval で計算可能

2. **リストの長さによる階層**
   - 基礎集合：List ℕ
   - 層 n = {l : List ℕ | l.length ≤ n}
   - minLayer(l) = l.length（長さを計算）
   - 実際に #eval で計算可能

## 計算可能性の重要性

構造塔理論において、minLayerが計算可能であることは：
- 理論的な存在証明だけでなく、実際に構成できることを示す
- Lean での検証可能性を高める
- 初学者が具体的な計算を通じて理解を深められる
- 圏論的な普遍性と計算可能性の両立を示す

## 数学的背景

構造塔は Bourbaki の構造理論に基づく概念で、集合に階層的な構造を与えます。
各要素が属する「最小の層」を選ぶ関数 minLayer を持つことで、
射の定義が一意になり、圏論的な普遍性が成り立ちます。
-/

/-!
## StructureTowerWithMin の定義（参考）

本ファイルで使用する構造塔の定義を再掲します。
実際の実装は CAT2_complete.lean を参照してください。
-/

/-- 最小層を持つ構造塔（簡易版） -/
structure StructureTowerWithMin where
  /-- 基礎集合 -/
  carrier : Type
  /-- 添字集合 -/
  Index : Type
  /-- 添字集合上の半順序 -/
  [indexPreorder : Preorder Index]
  /-- 各層の定義: Index → Set carrier -/
  layer : Index → Set carrier
  /-- 被覆性: すべての層の和集合が全体を覆う -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- 単調性: 順序を保存 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- 各要素の最小層を選ぶ関数 -/
  minLayer : carrier → Index
  /-- minLayer x は実際に x を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayer x は最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

end StructureTowerWithMin

/-!
## 例1: 整数の絶対値による構造塔

この例は、整数の「大きさ」を絶対値で測る自然な階層を示します。

### 数学的直感

整数を「原点からの距離」で分類すると：
- 層 0: {0}（原点のみ）
- 層 1: {-1, 0, 1}（距離1以内）
- 層 2: {-2, -1, 0, 1, 2}（距離2以内）
- 層 n: {k : ℤ | |k| ≤ n}

各整数 k の「本質的な位置」は |k| で決まります。
これが minLayer(k) = |k| の自然な定義です。

### 計算可能性

minLayer(k) = |k| は明示的に計算可能です：
- minLayer(5) = 5
- minLayer(-3) = 3
- minLayer(0) = 0
-/

/-- 整数の絶対値を計算する補助関数（計算可能） -/
def Int.absNat (z : ℤ) : ℕ :=
  Int.natAbs z

/-- 整数が特定の絶対値以下かを判定する（Decidable） -/
instance Int.decidableAbsLe (z : ℤ) (n : ℕ) : 
    Decidable (z ∈ {k : ℤ | Int.natAbs k ≤ n}) :=
  decidable_of_iff (Int.natAbs z ≤ n) (by simp [Set.mem_setOf])

/-- 整数の絶対値による構造塔

**層の定義**: layer(n) = {k : ℤ | |k| ≤ n}
**最小層**: minLayer(k) = |k|

この構造塔は以下を満たします：
1. 被覆性: すべての整数 k は層 |k| に属する
2. 単調性: n ≤ m ⇒ layer(n) ⊆ layer(m)
3. 最小性: |k| は k を含む最小の層の添字
-/
def intAbsTower : StructureTowerWithMin where
  carrier := ℤ
  Index := ℕ
  indexPreorder := inferInstance
  
  -- 層の定義: n 番目の層は絶対値 n 以下の整数
  layer := fun n => {k : ℤ | Int.natAbs k ≤ n}
  
  -- 被覆性: 任意の整数 k は層 |k| に属する
  covering := by
    intro k
    use Int.natAbs k
    -- k ∈ {k' : ℤ | |k'| ≤ |k|}
    simp [Set.mem_setOf]
  
  -- 単調性: n ≤ m ならば、絶対値 n 以下 ⊆ 絶対値 m 以下
  monotone := by
    intro n m hnm k hk
    -- k ∈ layer(n) すなわち |k| ≤ n
    -- hnm : n ≤ m より |k| ≤ m
    simp [Set.mem_setOf] at hk ⊢
    exact Nat.le_trans hk hnm
  
  -- 最小層: 整数 k の最小層は |k|
  minLayer := fun k => Int.natAbs k
  
  -- minLayer の正当性: |k| は k を含む層
  minLayer_mem := by
    intro k
    simp [Set.mem_setOf]
  
  -- minLayer の最小性: k ∈ layer(i) ならば |k| ≤ i
  minLayer_minimal := by
    intro k i hi
    -- hi : k ∈ layer(i) すなわち |k| ≤ i
    simp [Set.mem_setOf] at hi
    exact hi

/-! ### 計算例: 整数の絶対値階層 -/

-- minLayer の計算例
#eval intAbsTower.minLayer 0      -- 結果: 0
#eval intAbsTower.minLayer 5      -- 結果: 5
#eval intAbsTower.minLayer (-3)   -- 結果: 3
#eval intAbsTower.minLayer 42     -- 結果: 42
#eval intAbsTower.minLayer (-100) -- 結果: 100

/-- 層の包含関係を確認する補助関数 -/
def checkInLayer (tower : StructureTowerWithMin) 
    (x : tower.carrier) (i : tower.Index) 
    [Decidable (x ∈ tower.layer i)] : Bool :=
  decide (x ∈ tower.layer i)

-- 0 は層 0 に属する
#eval checkInLayer intAbsTower 0 0        -- true
#eval checkInLayer intAbsTower 0 1        -- true（単調性より）

-- 5 は層 5 に属するが、層 4 には属さない
#eval checkInLayer intAbsTower 5 5        -- true
#eval checkInLayer intAbsTower 5 4        -- false
#eval checkInLayer intAbsTower 5 6        -- true

-- -3 は層 3 に属する
#eval checkInLayer intAbsTower (-3) 3     -- true
#eval checkInLayer intAbsTower (-3) 2     -- false

/-!
### 基本的な性質（証明は略）

以下の性質が成り立ちます（証明は演習問題）：
-/

/-- 0 の最小層は 0 -/
lemma intAbsTower_zero : intAbsTower.minLayer 0 = 0 := by
  rfl

/-- 正の整数の最小層はその値自身 -/
lemma intAbsTower_pos (n : ℕ) : 
    intAbsTower.minLayer (n : ℤ) = n := by
  simp [intAbsTower]
  rfl

/-- 負の整数の最小層はその絶対値 -/
lemma intAbsTower_neg (n : ℕ) (hn : n ≠ 0) : 
    intAbsTower.minLayer (-(n : ℤ)) = n := by
  simp [intAbsTower]
  rfl

/-- 対称性: k と -k は同じ最小層を持つ -/
lemma intAbsTower_symm (k : ℤ) : 
    intAbsTower.minLayer k = intAbsTower.minLayer (-k) := by
  simp [intAbsTower]
  exact Int.natAbs_neg k

/-!
## 例2: リストの長さによる構造塔

この例は、有限列の「複雑さ」を長さで測る階層を示します。

### 数学的直感

自然数のリストを「長さ」で分類すると：
- 層 0: {[]}（空リストのみ）
- 層 1: {[], [a]}（長さ1以下）
- 層 2: {[], [a], [a,b]}（長さ2以下）
- 層 n: {l : List ℕ | l.length ≤ n}

各リスト l の「本質的な複雑さ」は l.length で決まります。

### 計算可能性

minLayer(l) = l.length は明示的に計算可能です：
- minLayer([]) = 0
- minLayer([1,2,3]) = 3
- minLayer([42]) = 1
-/

/-- リストが特定の長さ以下かを判定する（Decidable） -/
instance List.decidableLengthLe {α : Type} (l : List α) (n : ℕ) :
    Decidable (l ∈ {l' : List α | l'.length ≤ n}) :=
  decidable_of_iff (l.length ≤ n) (by simp [Set.mem_setOf])

/-- リストの長さによる構造塔

**層の定義**: layer(n) = {l : List ℕ | l.length ≤ n}
**最小層**: minLayer(l) = l.length

この構造塔は以下を示します：
1. 被覆性: すべてのリスト l は層 l.length に属する
2. 単調性: n ≤ m ⇒ layer(n) ⊆ layer(m)
3. 最小性: l.length は l を含む最小の層の添字
-/
def listLengthTower : StructureTowerWithMin where
  carrier := List ℕ
  Index := ℕ
  indexPreorder := inferInstance
  
  -- 層の定義: n 番目の層は長さ n 以下のリスト
  layer := fun n => {l : List ℕ | l.length ≤ n}
  
  -- 被覆性: 任意のリスト l は層 l.length に属する
  covering := by
    intro l
    use l.length
    simp [Set.mem_setOf]
  
  -- 単調性: n ≤ m ならば、長さ n 以下 ⊆ 長さ m 以下
  monotone := by
    intro n m hnm l hl
    simp [Set.mem_setOf] at hl ⊢
    exact Nat.le_trans hl hnm
  
  -- 最小層: リスト l の最小層は l.length
  minLayer := fun l => l.length
  
  -- minLayer の正当性
  minLayer_mem := by
    intro l
    simp [Set.mem_setOf]
  
  -- minLayer の最小性
  minLayer_minimal := by
    intro l i hi
    simp [Set.mem_setOf] at hi
    exact hi

/-! ### 計算例: リストの長さ階層 -/

-- minLayer の計算例
#eval listLengthTower.minLayer []                    -- 0
#eval listLengthTower.minLayer [1]                   -- 1
#eval listLengthTower.minLayer [1, 2, 3]             -- 3
#eval listLengthTower.minLayer [42, 0, 17, 3, 99]    -- 5

-- 層の包含関係を確認
#eval checkInLayer listLengthTower [] 0              -- true
#eval checkInLayer listLengthTower [] 1              -- true（単調性）
#eval checkInLayer listLengthTower [1,2,3] 3         -- true
#eval checkInLayer listLengthTower [1,2,3] 2         -- false
#eval checkInLayer listLengthTower [1,2,3] 10        -- true

/-!
### リスト階層の性質
-/

/-- 空リストの最小層は 0 -/
lemma listLengthTower_nil : 
    listLengthTower.minLayer [] = 0 := by
  rfl

/-- リストを追加すると最小層が1増加 -/
lemma listLengthTower_cons (a : ℕ) (l : List ℕ) :
    listLengthTower.minLayer (a :: l) = 
    listLengthTower.minLayer l + 1 := by
  simp [listLengthTower]
  exact List.length_cons a l

/-- リストの連結と最小層 -/
lemma listLengthTower_append (l₁ l₂ : List ℕ) :
    listLengthTower.minLayer (l₁ ++ l₂) =
    listLengthTower.minLayer l₁ + listLengthTower.minLayer l₂ := by
  simp [listLengthTower]
  exact List.length_append l₁ l₂

/-!
## 例3: 有限集合の濃度階層（概念的例）

次のような構造塔も自然に考えられます：

**基礎集合**: Finset ℕ（有限集合）
**層 n**: {S : Finset ℕ | S.card ≤ n}（濃度n以下）
**minLayer**: S ↦ S.card（集合の濃度）

この例も計算可能ですが、実装は読者への演習とします。
-/

/-!
## 計算的存在論の重要性

### 定理 vs 構成

古典数学では「存在する」という主張は、
「矛盾を導かない」ことで証明されることがあります。
しかし、構成的数学（Constructive Mathematics）では、
「存在する」は「具体的に構成できる」ことを意味します。

### 構造塔における計算可能性

構造塔理論において、minLayerが計算可能であることは：

1. **実装可能性**: 理論が単なる抽象論ではなく、実際に使える
2. **検証可能性**: Leanの #eval で動作を確認できる
3. **教育的価値**: 学習者が具体的な例で理解を深められる
4. **圏論との両立**: 抽象的な普遍性と具体的な計算が共存

### 本ファイルの意義

本ファイルで示した2つの例（整数の絶対値、リストの長さ）は：
- minLayer が明示的に計算可能
- 層の判定も decidable
- #eval で実際の動作を確認可能
- 数学的に自然で、構造塔の直感を提供
-/

/-!
## 学習のまとめ

### 重要なポイント

1. **minLayer の役割**
   - 各要素の「本質的な位置」を選ぶ
   - 構造塔の一意性を保証する鍵

2. **計算可能性の意義**
   - 理論と実装の橋渡し
   - Lean での完全な検証を可能にする

3. **具体例の価値**
   - 抽象理論の直感を養う
   - 形式化の妥当性を確認する

### 次のステップ

1. **他の計算可能な例を考える**
   - 多項式の次数階層
   - 有理数の分母階層
   - グラフの辺数階層

2. **射の構成を実装する**
   - 整数の倍数写像 k ↦ 2k
   - リストの連結 l ↦ l ++ [0]

3. **普遍性を具体例で確認する**
   - 自由構造塔の普遍性
   - 直積の普遍性

### 教育的メッセージ

形式数学は単なる記号の操作ではなく、
実際に計算可能で、動作を確認できる
「生きた数学」を提供します。

構造塔理論は、ブルバキの構造主義と
現代の計算可能性理論を統合する
良い例となっています。
-/

/-!
## 演習問題

### 基礎問題

1. minLayer の一意性を証明せよ：
   ∀ x i j, x ∈ layer i ∧ x ∈ layer j ∧ 
   (∀ k, x ∈ layer k → i ≤ k) ∧ (∀ k, x ∈ layer k → j ≤ k) → i = j

2. 単調性から以下を示せ：
   minLayer x ≤ i ↔ x ∈ layer i

### 応用問題

3. 整数の倍数写像 f(k) = 2k が構造塔の射を誘導することを示せ

4. 2つの整数の和が構造塔の積への射を定義することを確認せよ

5. 新しい計算可能な構造塔の例を実装せよ（例：多項式の次数）

### 発展問題

6. 構造塔の同型を構成し、その計算可能性を示せ

7. minLayer の計算量を解析せよ（本ファイルの例について）
-/

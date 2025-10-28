# Bourbaki流集合論的アプローチに基づくLean 4課題集

以下、段階的に難易度が上がる6つの課題を提示します。

---

## <exercise>

### <title>順序関係の基本性質：推移律の合成</title>

### <difficulty>初級</difficulty>

### <mathematical_statement>
集合 $E$ 上の二項関係 $R \subseteq E \times E$ が前順序(preorder)であるとは、次を満たすことである：
1. 反射性：$\forall x \in E, (x, x) \in R$
2. 推移性：$\forall x, y, z \in E, [(x, y) \in R \land (y, z) \in R] \Rightarrow (x, z) \in R$

**命題**：前順序関係 $R$ において、$x \leq y$ かつ $y \leq z$ ならば $x \leq z$ である。
</mathematical_statement>

### <lean_skeleton>
```lean
import Mathlib.Order.Basic

-- 前順序の定義はMathlib4に存在するが、明示的に証明する
variable {E : Type*} [Preorder E]

theorem preorder_transitivity (x y z : E) 
  (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  sorry
```
</lean_skeleton>

### <hints>
- `le_trans` タクティックまたは `Preorder` の推移性を直接利用
- `exact le_trans h1 h2` で証明完了
- Bourbakiの記法では関係を集合の部分集合として扱うが、Leanでは型クラスとして実装される
</hints>

### <bourbaki_reference>
『数学原論』第1部「集合論」第III章「順序構造」§1「順序関係の定義」
- 構造としての順序関係
- 反射性、反対称性、推移性の公理系
</bourbaki_reference>

</exercise>

---

## <exercise>

### <title>半順序集合における上界の一意性</title>

### <difficulty>初級〜中級</difficulty>

### <mathematical_statement>
半順序集合 $(E, \leq)$ と部分集合 $A \subseteq E$ に対して、$A$ の上界全体の集合を
$$\text{Upper}(A) = \{x \in E \mid \forall a \in A, a \leq x\}$$
と定義する。

**命題**：$A$ が最小上界(supremum) $s$ を持つならば、それは一意的である。すなわち、$s, s'$ が共に $A$ の最小上界ならば $s = s'$ である。
</mathematical_statement>

### <lean_skeleton>
```lean
import Mathlib.Order.Bounds.Basic

variable {E : Type*} [PartialOrder E]
variable (A : Set E)

theorem supremum_unique (s s' : E) 
  (hs : IsLUB A s) (hs' : IsLUB A s') : s = s' := by
  sorry

-- 別の定式化
theorem sSup_unique {s s' : E}
  (h1 : ∀ a ∈ A, a ≤ s) (h2 : ∀ x, (∀ a ∈ A, a ≤ x) → s ≤ x)
  (h1' : ∀ a ∈ A, a ≤ s') (h2' : ∀ x, (∀ a ∈ A, a ≤ x) → s' ≤ x) :
  s = s' := by
  sorry
```
</lean_skeleton>

### <hints>
- 最小上界の定義から、$s \leq s'$ かつ $s' \leq s$ を導く
- 半順序の反対称性を適用: `le_antisymm`
- `IsLUB` は `IsLeast (upperBounds A)` として定義されている
- 証明の鍵：各最小上界は他方の上界でもある
</hints>

### <bourbaki_reference>
『数学原論』第1部「集合論」第III章「順序構造」§2「最大元と最小元、上界と下界」
- 上界の概念
- 最小上界(borne supérieure)の一意性
- 順序集合における極値の理論
</bourbaki_reference>

</exercise>

---

## <exercise>

### <title>束における分配不等式</title>

### <difficulty>中級</difficulty>

### <mathematical_statement>
束(lattice) $(L, \leq, \lor, \land)$ において、任意の $x, y, z \in L$ に対して次の不等式が成立する：
$$x \land (y \lor z) \geq (x \land y) \lor (x \land z)$$

この不等式が等号で成り立つとき、束 $L$ は分配束(distributive lattice)と呼ばれる。
</mathematical_statement>

### <lean_skeleton>
```lean
import Mathlib.Order.Lattice

variable {L : Type*} [Lattice L]

-- すべての束で成り立つ不等式
theorem lattice_subdistributive (x y z : L) :
  (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z) := by
  sorry

-- 分配束の特徴付け
variable [DistribLattice L]

theorem distributive_law (x y z : L) :
  x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  sorry

-- 逆方向の分配法則も成立することを示す
theorem distributive_law_sup (x y z : L) :
  x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := by
  sorry
```
</lean_skeleton>

### <hints>
- 不等式の証明には `inf_le_left`, `inf_le_right`, `le_sup_left`, `le_sup_right` を使用
- `le_inf` と `sup_le` で上界・下界の性質を利用
- 分配束では `inf_sup_left` または `DistribLattice.le_antisymm` を使用
- 両方の分配法則は互いに導出可能
</hints>

### <bourbaki_reference>
『数学原論』第1部「集合論」第III章「順序構造」§3「束」
- 束の定義：上限と下限を持つ順序集合
- 分配束の特徴付け
- 束準同型と構造保存写像
</bourbaki_reference>

</exercise>

---

## <exercise>

### <title>群準同型による像の群構造</title>

### <difficulty>中級</difficulty>

### <mathematical_statement>
群 $(G, \cdot, e_G)$ から群 $(H, *, e_H)$ への写像 $f: G \to H$ が群準同型であるとは、
$$\forall x, y \in G, f(x \cdot y) = f(x) * f(y)$$
を満たすことである。

**定理**：$f: G \to H$ が群準同型ならば、$f$ の像 $\text{Im}(f) = \{f(x) \mid x \in G\} \subseteq H$ は $H$ の部分群である。
</mathematical_statement>

### <lean_skeleton>
```lean
import Mathlib.GroupTheory.Subgroup.Basic

variable {G H : Type*} [Group G] [Group H]
variable (f : G →* H)  -- 群準同型

-- 像が部分群であることの証明
theorem image_is_subgroup : IsSubgroup (Set.range f) := by
  sorry

-- または、MonoidHomを使った別の定式化
theorem range_is_subgroup : Subgroup H :=
  MonoidHom.range f

-- 単位元が像に含まれることの証明
theorem one_mem_image : (1 : H) ∈ Set.range f := by
  sorry

-- 像の元の逆元も像に含まれる
theorem inv_mem_image {h : H} (hh : h ∈ Set.range f) : 
  h⁻¹ ∈ Set.range f := by
  sorry
```
</lean_skeleton>

### <hints>
- 部分群の公理を確認：単位元の存在、逆元の存在、演算での閉性
- `MonoidHom.map_one` で $f(e_G) = e_H$ を使用
- `MonoidHom.map_mul` で準同型性を使用
- `MonoidHom.map_inv` で逆元の保存を使用
- Mathlib4では `MonoidHom.range` が既に部分群として定義されている
</hints>

### <bourbaki_reference>
『数学原論』第1部「集合論」第IV章「代数構造」§1「群とモノイド」
- 群の定義：集合と結合的演算、単位元、逆元
- 準同型写像の概念
- 部分群と像・核の理論
- 構造を保つ写像の基本性質
</bourbaki_reference>

</exercise>

---

## <exercise>

### <title>位相空間におけるコンパクト集合の閉性</title>

### <difficulty>中級〜上級</difficulty>

### <mathematical_statement>
位相空間 $(X, \mathcal{T})$ が Hausdorff空間であるとは、任意の相異なる2点 $x, y \in X$ ($x \neq y$) に対して、開集合 $U, V \in \mathcal{T}$ が存在して
$$x \in U, \quad y \in V, \quad U \cap V = \emptyset$$
を満たすことである。

**定理**：Hausdorff空間 $X$ において、コンパクト部分集合 $K \subseteq X$ は閉集合である。
</mathematical_statement>

### <lean_skeleton>
```lean
import Mathlib.Topology.Separation

variable {X : Type*} [TopologicalSpace X] [T2Space X]

-- コンパクト集合の閉性
theorem compact_is_closed {K : Set X} (hK : IsCompact K) : 
  IsClosed K := by
  sorry

-- または、別の定式化
theorem isCompact_isClosed {K : Set X} (h : IsCompact K) :
  IsClosed K := by
  rw [← isOpen_compl_iff]
  sorry

-- より具体的に：点がコンパクト集合の外にあれば、
-- 開近傍で分離できる
theorem exists_open_nhds_disjoint_of_not_mem_compact 
  {x : X} {K : Set X} (hK : IsCompact K) (hx : x ∉ K) :
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ 
    x ∈ U ∧ K ⊆ V ∧ Disjoint U V := by
  sorry
```
</lean_skeleton>

### <hints>
- Hausdorff性を使って、$x \notin K$ なる点 $x$ と各 $y \in K$ を分離する開集合を取る
- コンパクト性から有限個の開被覆を取り出す
- これらの開集合の共通部分を使って $x$ と $K$ を分離
- `T2Space.t2` でHausdorff性を利用
- `IsCompact.elim_finite_subcover` でコンパクト性を利用
- Mathlib4では `IsCompact.isClosed` として既に証明済み
</hints>

### <bourbaki_reference>
『数学原論』第1部「集合論」第IX章「位相空間の利用」§3「コンパクト空間」
- Hausdorff空間(分離公理 $T_2$)の定義
- コンパクト性の定義(開被覆の有限部分被覆)
- 分離性とコンパクト性の相互作用
- 位相構造における基本定理
</bourbaki_reference>

</exercise>

---

## <exercise>

### <title>有限直積のコンパクト性（Tychonoffの定理の有限版）</title>

### <difficulty>上級</difficulty>

### <mathematical_statement>
位相空間の族 $(X_i, \mathcal{T}_i)_{i \in I}$ の直積空間 $\prod_{i \in I} X_i$ に直積位相を入れる。直積位相は、各射影 $\pi_i: \prod_{j \in I} X_j \to X_i$ が連続となる最弱の位相である。

**定理（Tychonoff、有限版）**：有限個の位相空間 $X_1, \ldots, X_n$ がすべてコンパクトならば、その直積 $X_1 \times \cdots \times X_n$ もコンパクトである。

集合論的には、コンパクト空間の族 $(K_i)_{i=1}^n$ に対し、
$$K = \prod_{i=1}^n K_i = \{(x_1, \ldots, x_n) \mid x_i \in K_i\}$$
は直積位相に関してコンパクトである。
</mathematical_statement>

### <lean_skeleton>
```lean
import Mathlib.Topology.Constructions

-- 2つのコンパクト空間の直積
theorem compact_prod {X Y : Type*} 
  [TopologicalSpace X] [TopologicalSpace Y]
  {K : Set X} {L : Set Y}
  (hK : IsCompact K) (hL : IsCompact L) :
  IsCompact (K ×ˢ L) := by
  sorry

-- 有限直積への一般化（帰納的定義）
theorem compact_pi_finite {ι : Type*} {X : ι → Type*}
  [Finite ι] [∀ i, TopologicalSpace (X i)]
  {K : ∀ i, Set (X i)} (hK : ∀ i, IsCompact (K i)) :
  IsCompact (Set.pi Set.univ K) := by
  sorry

-- 具体的な3次元の場合
theorem compact_prod3 {X Y Z : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (hX : CompactSpace X) (hY : CompactSpace Y) (hZ : CompactSpace Z) :
  CompactSpace (X × Y × Z) := by
  sorry
```
</lean_skeleton>

### <hints>
- 2つの場合の証明：開被覆 $\{U_\alpha\}$ を基本開集合 $V \times W$ の形で近似
- 各 $x \in K$ に対して有限個の基本開集合で覆える
- $K$ のコンパクト性から有限部分被覆を取る
- 帰納法で一般の有限直積に拡張
- Mathlib4では `IsCompact.prod` として証明済み
- 直積位相の定義：`Pi.topologicalSpace`, `Prod.topologicalSpace`
- 射影の連続性を利用
</hints>

### <bourbaki_reference>
『数学原論』第1部「集合論」第IX章「位相空間の利用」
- §4「直積空間」：直積位相の構成
- §3「コンパクト空間」：Tychonoffの定理
- 有限直積から無限直積への拡張（選択公理の使用）
- 一般位相幾何学における基本定理の一つ
- 構造の直積としての圏論的視点
</bourbaki_reference>

</exercise>

---

## 補足：Bourbaki的アプローチの特徴

これらの課題は以下のBourbaki的原則に従っています：

1. **構造の階層性**：前順序 → 半順序 → 束 → 分配束のような段階的発展
2. **集合論的基礎**：すべての概念を集合、関係、写像で表現
3. **抽象化と一般化**：具体例より一般的な構造を優先
4. **公理的方法**：構造を満たすべき公理系として定義
5. **普遍性**：準同型、積、極限など、普遍的性質による特徴付け

Lean 4での実装では、これらの抽象概念が型クラスとして実現され、Mathlib4が豊富な定理ライブラリを提供しています。
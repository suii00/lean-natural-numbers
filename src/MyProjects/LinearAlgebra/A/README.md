# 線形代数タスク（A）数学的解説 — ブルバキ的視点（順序対と射）

本ディレクトリの 3 つの Lean ファイルは、ニコラ・ブルバキ『数学原論』の精神、すなわち
「順序対（構成物）を射影で読み、構造は射のふるまいで規定される」という観点で記述している。
用いる事実はいずれも mathlib の標準補題（線形性、加法性、評価の性質）で、
余計な定義を導入せず“射を通して読む”ことに徹している。

---

## 1. 合成の線形性（lean_composition_task.lean）

- 対象: `R`-加群 `U, V, W` と線形写像 `f : U →ₗ[R] V`, `g : V →ₗ[R] W`。
- 主要命題:
  - `comp_preserves_linearity`: 合成 `g.comp f` は加法を保つ（`map_add`）。
  - `comp_assoc`: 合成は結合的 `((h.comp g).comp f) = h.comp (g.comp f)`。
  - `comp_id_left`: 恒等との合成 `LinearMap.id.comp f = f`。

証明の核は「射としての線形写像の公理」：

- 和に関する線形性は `LinearMap.map_add` によって、定義から即座に得られる。
- 合成の結合律・恒等律は、関数合成としての定義から `ext` によって各元で一致することを示せばよい。

ブルバキ的読み方: 対象 `U` の元 `u` を「射 `f` で `V` に送り、さらに `g` で `W` に送る」。
等式は、順序対の各成分を見るかわりに「値の通り道（射の連鎖）」を追うことで成分的に検証される。

参照補題（mathlib）: `LinearMap.map_add`, `LinearMap.comp`, `LinearMap.ext`。

---

## 2. 核と像の閉性（lean_kernel_image_task.lean）

- 対象: 線形写像 `f : V →ₗ[R] W`。
- 主要命題:
  - `ker_is_submodule`: `v, w ∈ ker f ⇒ v + w ∈ ker f`（加法閉性）。
  - `range_is_submodule`: `y, z ∈ range f ⇒ y + z ∈ range f`（加法閉性）。
  - `ker_smul_closed`: `v ∈ ker f ⇒ a • v ∈ ker f`（スカラー倍閉性）。

核と像の定義（射で読む）:

- `ker f` は「`f` で零に射影される元の集合」：`v ∈ ker f ↔ f v = 0`（`LinearMap.mem_ker`）。
- `range f` は「ある `v` が存在して `f v = y`」という存在表示（`LinearMap.mem_range`）。

証明の要点:

- 核の加法閉性は `f (v + w) = f v + f w`（`map_add`）と `f v = 0`, `f w = 0` の合成で直ちに従う。
- 像の加法閉性は `y = f v`, `z = f w` から `y + z = f (v + w)` を構成（`map_add`）。
- 核のスカラー倍閉性は部分加群としての一般性 `Submodule.smul_mem` による。

参照補題: `LinearMap.mem_ker`, `LinearMap.range`, `LinearMap.map_add`,
`Submodule.smul_mem`。

---

## 3. 双対空間と評価（lean_dual_space_task.lean）

- 対象: 双対 `Module.Dual R V = (V →ₗ[R] R)`。
- 主要命題:
  - `dual_add_is_linear`: 汎関数の和は点ごとに加法的：`(φ + ψ) v = φ v + ψ v`。
  - `eval_map_is_linear`: 上式の対称形（右辺と左辺の入れ替え）。
  - `double_dual_eval`: 二重双対評価 `Module.Dual.eval R V v φ = φ v`。
  - `dual_pairing_bilinear`: ペアリング `⟨φ, v⟩ = φ v` の双線形性
    `φ (a • v + w) = a * φ v + φ w`。

ブルバキ的読み方: 双対空間は「値 `R` に至る射の集合」であり、
和・スカラー倍は射の演算として定まる。評価 `eval` は「`v` を固定して `φ ↦ φ v` と読む」
線形写像であり、二重双対評価はその定義そのものに等しい（`eval_apply`）。

参照補題: `LinearMap.add_apply`, `Module.Dual.eval_apply`, `LinearMap.map_add`,
`LinearMap.map_smul`, `smul_eq_mul`。

---

## 付記（import の最小化）

mathlib4 では API の所在が細分化されているため、以下を最小限として採用している：

- 合成・核・像・双対の基本:
  - `Mathlib.Algebra.Module.LinearMap.Defs`
  - `Mathlib.Algebra.Module.LinearMap.Basic`
- 核と像の定義と補題:
  - `Mathlib.Algebra.Module.Submodule.Ker`
  - `Mathlib.Algebra.Module.Submodule.Range`
- 双対の定義と評価:
  - `Mathlib.LinearAlgebra.Dual.Defs`

これにより、証明はすべて「射の公理（map_add / map_smul / eval）」に還元され、
順序対や射影による“成分で読む”作法と整合する。


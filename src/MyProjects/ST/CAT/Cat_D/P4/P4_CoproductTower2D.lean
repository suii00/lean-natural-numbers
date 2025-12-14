import MyProjects.ST.CAT.Cat_D.P4.P4_Categorical

/-!
# P4_CoproductTower2D: `Index := Prod` による「2次元」余積塔

このファイルは `P4_Categorical.lean` の定義（`TowerD`, `HomD` など）を再利用し、
台集合が直和 `T₁.carrier ⊕ T₂.carrier` で、添字が直積 `T₁.Index × T₂.Index` の
“2次元パラメータ付き” の構造塔を定義する。

## 主な定義

- `coprodTower₂D`:
  - `carrier := T₁.carrier ⊕ T₂.carrier`
  - `Index := T₁.Index × T₂.Index`
  - `layer (i, j) := (Sum.inl '' T₁.layer i) ∪ (Sum.inr '' T₂.layer j)`

## 注意（普遍性）

これは一般には Cat_D における「余積（coproduct）」の普遍性を主張しない。
`HomD.map_layer` は “1 つの上界” を要求するため、左右の上界を 1 つにまとめるには
ターゲット側の添字に 2 元の上界が存在する、等の追加仮定が必要になる。

（ブルバキ的には：まず集合論的な構成を与え、普遍性は必要な追加公理の下で別途述べる。）
-/

namespace ST
namespace TowerD

section CoproductTower2D

/-- `Index := Prod` 版の「2次元」余積塔

`(i, j)` で左右の層の複雑さを同時に管理するための構成であり、
`Sum` 版（`coprod`）のような余積の普遍性は一般には保証しない。

定義のために、反対側の添字を埋める `default` が必要なので `Inhabited` を仮定する。
-/
def coprodTower₂D (T₁ T₂ : TowerD) [Inhabited T₁.Index] [Inhabited T₂.Index] : TowerD where
  carrier := T₁.carrier ⊕ T₂.carrier
  Index := T₁.Index × T₂.Index
  indexPreorder := inferInstanceAs (Preorder (T₁.Index × T₂.Index))
  layer := fun ⟨i, j⟩ => (Sum.inl '' (T₁.layer i)) ∪ (Sum.inr '' (T₂.layer j))
  covering := by
    intro x
    cases x with
    | inl x₁ =>
      obtain ⟨i, hi⟩ := T₁.covering x₁
      refine ⟨⟨i, default⟩, ?_⟩
      exact Or.inl ⟨x₁, hi, rfl⟩
    | inr x₂ =>
      obtain ⟨j, hj⟩ := T₂.covering x₂
      refine ⟨⟨default, j⟩, ?_⟩
      exact Or.inr ⟨x₂, hj, rfl⟩
  monotone := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hij x hx
    rcases hij with ⟨hi, hj⟩
    rcases hx with hx | hx
    · rcases hx with ⟨a, ha, rfl⟩
      exact Or.inl ⟨a, T₁.monotone hi ha, rfl⟩
    · rcases hx with ⟨b, hb, rfl⟩
      exact Or.inr ⟨b, T₂.monotone hj hb, rfl⟩

notation:35 T₁ " ⊕₂ᴰ " T₂ => coprodTower₂D T₁ T₂

/-- `coprodTower₂D` への第1埋め込み -/
def inj₁₂D (T₁ T₂ : TowerD) [Inhabited T₁.Index] [Inhabited T₂.Index] :
    T₁ ⟶ᴰ (T₁ ⊕₂ᴰ T₂) where
  map := Sum.inl
  map_layer := by
    intro i
    refine ⟨(i, default), ?_⟩
    intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    exact Or.inl ⟨a, ha, rfl⟩

/-- `coprodTower₂D` への第2埋め込み -/
def inj₂₂D (T₁ T₂ : TowerD) [Inhabited T₁.Index] [Inhabited T₂.Index] :
    T₂ ⟶ᴰ (T₁ ⊕₂ᴰ T₂) where
  map := Sum.inr
  map_layer := by
    intro j
    refine ⟨(default, j), ?_⟩
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    exact Or.inr ⟨b, hb, rfl⟩

end CoproductTower2D

section Examples

-- 最小の動作確認（コンパイル用）
example : TowerD := natTower ⊕₂ᴰ natTower

example : (inj₁₂D natTower natTower).map (5 : ℕ) = Sum.inl 5 := rfl

example : Sum.inl (2 : ℕ) ∈ (natTower ⊕₂ᴰ natTower).layer ((2 : ℕ), (0 : ℕ)) := by
  -- 左成分の layer (2, 0) に入ることだけを示せばよい
  simp [coprodTower₂D]

end Examples

end TowerD
end ST

import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Order.Basic
import Mathlib.Data.String.Basic

/-
# Computable structure towers

This file gives Bourbaki-flavoured, mostly computable examples of
`StructureTowerWithMin`.  The integer / list / finset / string sections are
executable (`#eval`) and free of `sorry`; the polynomial section uses
`natDegree` and therefore lives in a `noncomputable` context, but remains
fully checked by Lean.

## Contents
* Integer tower stratified by absolute value.
* List tower stratified by length.
* Finite-set tower stratified by cardinality.
* Polynomial tower stratified by degree.
* String tower stratified by length.

Each tower supplies explicit decidable membership and a concrete `minLayer`,
emphasising constructive set-theoretic structure.
-/

/-
## Reminder: `StructureTowerWithMin`

Restated for convenience; the authoritative version lives in
`CAT2_complete.lean`.
-/

/-- A structure tower equipped with a choice of minimal layer. -/
structure StructureTowerWithMin where
  /-- Underlying set. -/
  carrier : Type
  /-- Indexing set. -/
  Index : Type
  /-- Order on indices. -/
  [indexPreorder : Preorder Index]
  /-- The n-th layer. -/
  layer : Index → Set carrier
  /-- Covering: every element lives in some layer. -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- Monotonicity of layers. -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- Minimal layer selector. -/
  minLayer : carrier → Index
  /-- Soundness: `minLayer x` really contains `x`. -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- Minimality: `minLayer x` is the smallest index containing `x`. -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

/-- Minimal layer is unique up to antisymmetry: any other minimal index differs
    from `minLayer x` by a pair of inequalities. Use `le_antisymm` when the
    index order is antisymmetric. -/
lemma minLayer_unique (T : StructureTowerWithMin)
    (x : T.carrier) (i : T.Index)
    (hi : x ∈ T.layer i) (hmin : ∀ k, x ∈ T.layer k → i ≤ k) :
    i ≤ T.minLayer x ∧ T.minLayer x ≤ i :=
  ⟨hmin _ (T.minLayer_mem x), T.minLayer_minimal x i hi⟩

/-- Membership is equivalent to being above the minimal layer. -/
lemma minLayer_le_iff (T : StructureTowerWithMin) (x : T.carrier) (i : T.Index) :
    T.minLayer x ≤ i ↔ x ∈ T.layer i := by
  constructor
  · intro hle
    exact T.monotone hle (T.minLayer_mem x)
  · intro hi
    exact T.minLayer_minimal x i hi

/-- Morphisms of structure towers preserving layers and minimal layers. -/
structure Hom (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving :
    ∀ {x i}, x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving :
    ∀ x, indexMap (T.minLayer x) = T'.minLayer (map x)

/-- Extensionality for tower homomorphisms. -/
@[ext] theorem Hom.ext {T T'} (f g : Hom T T')
    (hmap : f.map = g.map) (hidx : f.indexMap = g.indexMap) : f = g := by
  cases f; cases g; cases hmap; cases hidx; rfl

/-- Identity homomorphism of a structure tower. -/
def Hom.id (T : StructureTowerWithMin) : Hom T T where
  map := fun x => x
  indexMap := fun i => i
  indexMap_mono := fun h => h
  layer_preserving := by intro x i hi; simpa using hi
  minLayer_preserving := by intro x; rfl

/-- Composition of structure-tower homomorphisms. -/
def Hom.comp {T₁ T₂ T₃ : StructureTowerWithMin}
    (g : Hom T₂ T₃) (f : Hom T₁ T₂) : Hom T₁ T₃ where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := by
    intro i j h
    exact g.indexMap_mono (f.indexMap_mono h)
  layer_preserving := by
    intro x i hi
    exact g.layer_preserving (f.layer_preserving hi)
  minLayer_preserving := by
    intro x
    calc
      g.indexMap (f.indexMap (T₁.minLayer x))
          = g.indexMap (T₂.minLayer (f.map x)) := by
              simpa using congrArg g.indexMap (f.minLayer_preserving x)
      _ = T₃.minLayer (g.map (f.map x)) := by
              simpa using g.minLayer_preserving (f.map x)

/-- Associativity of hom composition. -/
@[simp] lemma Hom.comp_assoc {T₁ T₂ T₃ T₄ : StructureTowerWithMin}
    (h₁ : Hom T₁ T₂) (h₂ : Hom T₂ T₃) (h₃ : Hom T₃ T₄) :
    Hom.comp h₃ (Hom.comp h₂ h₁) = Hom.comp (Hom.comp h₃ h₂) h₁ := by
  rfl

/-- Left identity for hom composition. -/
@[simp] lemma Hom.id_comp {T₁ T₂ : StructureTowerWithMin} (f : Hom T₁ T₂) :
    Hom.comp (Hom.id T₂) f = f := rfl

/-- Right identity for hom composition. -/
@[simp] lemma Hom.comp_id {T₁ T₂ : StructureTowerWithMin} (f : Hom T₁ T₂) :
    Hom.comp f (Hom.id T₁) = f := rfl

/-- Image of a layer element via a hom. -/
lemma Hom.map_mem_layer {T T' : StructureTowerWithMin}
    (h : Hom T T') {x i} (hx : x ∈ T.layer i) :
    h.map x ∈ T'.layer (h.indexMap i) :=
  h.layer_preserving hx

/-- minLayer equality transported along a hom. -/
lemma Hom.map_minLayer {T T' : StructureTowerWithMin}
    (h : Hom T T') (x : T.carrier) :
    h.indexMap (T.minLayer x) = T'.minLayer (h.map x) :=
  h.minLayer_preserving x

/--
`HomLe` は `StructureTowerWithMin` 間の「上限保存射」を表す。

ふつうの `Hom` は
  T'.minLayer (map x) = indexMap (T.minLayer x)
という等式を要求するのに対し，
`HomLe` は
  T'.minLayer (map x) ≤ indexMap (T.minLayer x)
という不等式だけを要求する。

これにより，次のような「層を潰す／拡げる」射を一つの枠組みで扱える：
* 整数塔の平行移動 `k ↦ k + a` （`|k + a| ≤ |k| + |a|`）
* 多項式塔の加法 `p + q` （`deg (p + q) ≤ max (deg p) (deg q)`）
* 多項式塔の 0 倍 `p ↦ 0` （minLayer が下がるが，上界は 0 で与えられる）

`Hom` は「すべての像で minLayer が等式になる HomLe」と見なせるので，HomLe は構造塔に現れる射の自然な一般化になっている。
-/
structure HomLe (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving :
    ∀ {x i}, x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_le :
    ∀ x, T'.minLayer (map x) ≤ indexMap (T.minLayer x)

/-- Extensionality for `HomLe`. -/
@[ext] lemma HomLe.ext {T T' : StructureTowerWithMin} (f g : HomLe T T')
    (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) : f = g := by
  cases f; cases g; cases hmap; cases hindex; rfl

/-- Forgetful map from `Hom` to `HomLe`. -/
def Hom.toHomLe {T T' : StructureTowerWithMin} (h : Hom T T') : HomLe T T' :=
{ map := h.map
  indexMap := h.indexMap
  indexMap_mono := h.indexMap_mono
  layer_preserving := h.layer_preserving
  minLayer_le := by
    intro x
    simpa [h.minLayer_preserving x] using le_of_eq (h.minLayer_preserving x) }

/-- Identity morphism for `HomLe`. -/
def HomLe.id (T : StructureTowerWithMin) : HomLe T T :=
{ map := fun x => x
  indexMap := fun i => i
  indexMap_mono := fun h => h
  layer_preserving := by intro x i hi; simpa using hi
  minLayer_le := by intro x; exact le_rfl }

/-- Composition for `HomLe`. -/
def HomLe.comp {T₁ T₂ T₃ : StructureTowerWithMin}
    (g : HomLe T₂ T₃) (f : HomLe T₁ T₂) : HomLe T₁ T₃ :=
{ map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := by
    intro i j h; exact g.indexMap_mono (f.indexMap_mono h)
  layer_preserving := by
    intro x i hi; exact g.layer_preserving (f.layer_preserving hi)
  minLayer_le := by
    intro x
    calc
      T₃.minLayer (g.map (f.map x))
          ≤ g.indexMap (T₂.minLayer (f.map x)) := g.minLayer_le _
      _ ≤ g.indexMap (f.indexMap (T₁.minLayer x)) :=
        g.indexMap_mono (f.minLayer_le x) }

/-- Product of two structure towers (componentwise layers). -/
def prod (T₁ T₂ : StructureTowerWithMin) : StructureTowerWithMin where
  carrier := T₁.carrier × T₂.carrier
  Index := T₁.Index × T₂.Index
  indexPreorder := inferInstance
  layer := fun ij =>
    {p : T₁.carrier × T₂.carrier |
      p.1 ∈ T₁.layer ij.1 ∧ p.2 ∈ T₂.layer ij.2}
  covering := by
    intro p
    rcases T₁.covering p.1 with ⟨i, hi⟩
    rcases T₂.covering p.2 with ⟨j, hj⟩
    refine ⟨(i, j), ?_⟩
    exact ⟨hi, hj⟩
  monotone := by
    intro i j hij p hp
    exact ⟨T₁.monotone hij.1 hp.1, T₂.monotone hij.2 hp.2⟩
  minLayer := fun p => (T₁.minLayer p.1, T₂.minLayer p.2)
  minLayer_mem := by
    intro p
    exact ⟨T₁.minLayer_mem _, T₂.minLayer_mem _⟩
  minLayer_minimal := by
    intro p ij hp
    exact ⟨T₁.minLayer_minimal _ _ hp.1, T₂.minLayer_minimal _ _ hp.2⟩

end StructureTowerWithMin

/-
## Example 1: integers stratified by absolute value

Layers are determined by distance from the origin:
* layer 0  : `{0}`
* layer 1  : `{-1, 0, 1}`
* layer 2  : `{-2, -1, 0, 1, 2}`
* layer n  : `{k : ℤ | |k| ≤ n}`

The essential position of `k` is `|k|`, so `minLayer k = |k|`.
-/

/-- Helper: absolute value as a natural number (computable). -/
def Int.absNat (z : ℤ) : ℕ :=
  Int.natAbs z

/-- Decidable membership in the predicate `|k| ≤ n`. -/
instance Int.decidableAbsLe (z : ℤ) (n : ℕ) :
    Decidable (z ∈ {k : ℤ | Int.natAbs k ≤ n}) :=
  decidable_of_iff (Int.natAbs z ≤ n) (by simp)

/-- Structure tower ordered by absolute value. -/
abbrev intAbsTower : StructureTowerWithMin where
  carrier := ℤ
  Index := ℕ
  indexPreorder := inferInstance

  -- layer n: integers whose absolute value is at most n
  layer := fun n => {k : ℤ | Int.natAbs k ≤ n}

  -- covering: every integer lies in its own `|k|` layer
  covering := by
    intro k
    use Int.natAbs k
    simp

  -- monotone: n ≤ m ⇒ layer n ⊆ layer m
  monotone := by
    intro n m hnm k hk
    simp at hk ⊢
    exact Nat.le_trans hk hnm

  -- minimal layer: `|k|`
  minLayer := fun k => Int.natAbs k

  -- soundness
  minLayer_mem := by
    intro k
    simp

  -- minimality
  minLayer_minimal := by
    intro k i hi
    simp at hi
    exact hi

/-! ### Sample computations: integer tower -/

instance (k : ℤ) (n : ℕ) : Decidable (k ∈ intAbsTower.layer n) := by
  dsimp [intAbsTower]
  infer_instance

-- minLayer examples
#eval intAbsTower.minLayer (0 : ℤ)      -- 0
#eval intAbsTower.minLayer (5 : ℤ)      -- 5
#eval intAbsTower.minLayer (-3 : ℤ)     -- 3
#eval intAbsTower.minLayer (42 : ℤ)     -- 42
#eval intAbsTower.minLayer (-100 : ℤ)   -- 100

/-- Helper: check membership in a tower layer as a `Bool`. -/
def checkInLayer (tower : StructureTowerWithMin)
    (x : tower.carrier) (i : tower.Index)
    [Decidable (x ∈ tower.layer i)] : Bool :=
  decide (x ∈ tower.layer i)

/-- Specialized, fully computable membership for the integer tower. -/
def checkIntLayer (k : ℤ) (n : ℕ) : Bool :=
  decide (Int.natAbs k ≤ n)

-- membership checks
#eval checkIntLayer (0 : ℤ) (0 : ℕ)        -- true
#eval checkIntLayer (0 : ℤ) (1 : ℕ)        -- true (monotone)
#eval checkIntLayer (5 : ℤ) (5 : ℕ)        -- true
#eval checkIntLayer (5 : ℤ) (4 : ℕ)        -- false
#eval checkIntLayer (5 : ℤ) (6 : ℕ)        -- true
#eval checkIntLayer (-3 : ℤ) (3 : ℕ)       -- true
#eval checkIntLayer (-3 : ℤ) (2 : ℕ)       -- false

/-! Basic properties -/

/-- The minimal layer of 0 is 0. -/
lemma intAbsTower_zero : intAbsTower.minLayer (0 : ℤ) = 0 := by
  simp [intAbsTower]

/-- Positive integers live in their own layer. -/
lemma intAbsTower_pos (n : ℕ) :
    intAbsTower.minLayer (n : ℤ) = n := by
  simp [intAbsTower]

/-- Negative integers sit in the layer indexed by their absolute value. -/
lemma intAbsTower_neg (n : ℕ) :
    intAbsTower.minLayer (-(n : ℤ)) = n := by
  simp [intAbsTower]

/-- Symmetry: `k` and `-k` share the same minimal layer. -/
lemma intAbsTower_symm (k : ℤ) :
    intAbsTower.minLayer k = intAbsTower.minLayer (-k) := by
  simp [intAbsTower]

/-! HomLe example: integer translation (additive action up to an upper bound). -/

/-- Addition by a fixed integer as an upper-bound-preserving morphism. -/
def intAddHomLe (a : ℤ) : StructureTowerWithMin.HomLe intAbsTower intAbsTower :=
{ map := fun k => k + a
  indexMap := fun n => n + Int.natAbs a
  indexMap_mono := by
    intro i j h; exact Nat.add_le_add_right h _
  layer_preserving := by
    intro k n hk
    have htriangle : Int.natAbs (k + a) ≤ Int.natAbs k + Int.natAbs a :=
      Int.natAbs_add_le k a
    have hbound : Int.natAbs k + Int.natAbs a ≤ n + Int.natAbs a :=
      Nat.add_le_add_right hk _
    exact Nat.le_trans htriangle hbound
  minLayer_le := by
    intro k
    simpa using Int.natAbs_add_le k a }

-- sample checks
#eval (intAddHomLe 3).map (-2)          -- 1
#eval (intAddHomLe (-5)).indexMap 4     -- 9
#eval checkInLayer intAbsTower ((intAddHomLe 3).map 5) ((intAddHomLe 3).indexMap 5)

lemma intAddHomLe_zero :
    intAddHomLe 0 = StructureTowerWithMin.HomLe.id intAbsTower := by
  ext k n <;> simp [intAddHomLe, StructureTowerWithMin.HomLe.id]

/-! ### Morphism-style computations (exercise hints) -/

/-- Doubling map sends layer `n` into layer `2*n` (computable check). -/
def doubleRespectsLayers (k : ℤ) (n : ℕ) : Bool :=
  checkIntLayer (2 * k) (2 * n)

-- examples
#eval doubleRespectsLayers (3 : ℤ) 3   -- true, |6| ≤ 6
#eval doubleRespectsLayers (-4 : ℤ) 3  -- true, |−8| ≤ 6 is false → returns false

/-- Addition into the product tower: `k₁ + k₂` lies in layer `|k₁|+|k₂|`. -/
def addRespectsLayers (k₁ k₂ : ℤ) : Bool :=
  checkIntLayer (k₁ + k₂) (Int.natAbs k₁ + Int.natAbs k₂)

-- examples
#eval addRespectsLayers (2 : ℤ) 3     -- true
#eval addRespectsLayers (-5 : ℤ) 4    -- true
#eval addRespectsLayers (7 : ℤ) (-2)  -- true

/-- Doubling as a morphism of integer towers. -/
def intAbsTowerDouble : StructureTowerWithMin.Hom intAbsTower intAbsTower :=
{ map := fun k => 2 * k
  indexMap := fun n => 2 * n
  indexMap_mono := by
    intro i j hij
    exact Nat.mul_le_mul_left 2 hij
  layer_preserving := by
    intro k n hk
    -- |2k| = 2 * |k| ≤ 2n
    have h' : Int.natAbs (2 * k) = 2 * Int.natAbs k := by
      simpa using Int.natAbs_mul (2) k
    have hk' : 2 * Int.natAbs k ≤ 2 * n :=
      Nat.mul_le_mul_left 2 hk
    dsimp [intAbsTower]
    simp [h', hk']
  minLayer_preserving := by
    intro k
    dsimp [intAbsTower]
    have h' : Int.natAbs (2 * k) = 2 * Int.natAbs k := by
      simpa using Int.natAbs_mul (2) k
    simp [h'] }

/-- Diagonal map into the product integer tower. -/
def intAbsTowerDiag :
    StructureTowerWithMin.Hom intAbsTower
      (StructureTowerWithMin.prod intAbsTower intAbsTower) :=
{ map := fun k => (k, k)
  indexMap := fun n => (n, n)
  indexMap_mono := by
    intro i j h
    exact ⟨h, h⟩
  layer_preserving := by
    intro k n hk
    dsimp [StructureTowerWithMin.prod, intAbsTower] at *
    -- goal is conjunction of the same inequality
    exact ⟨hk, hk⟩
  minLayer_preserving := by
    intro k
    rfl }

-- sample morphism computations
#eval intAbsTowerDouble.indexMap 5    -- 10
#eval intAbsTowerDouble.map (-3)      -- -6
#eval intAbsTowerDiag.indexMap 4      -- (4, 4)

/-
## Example 2: lists stratified by length

Finite sequences are organised by length:
* layer 0  : `{[]}`
* layer 1  : `{[], [a]}`
* layer 2  : `{[], [a], [a,b]}`
* layer n  : `{l : List ℕ | l.length ≤ n}`

Here the complexity measure is length itself, so `minLayer l = l.length`.
-/

/-- Decidable membership in the predicate `length ≤ n`. -/
instance List.decidableLengthLe {α : Type} (l : List α) (n : ℕ) :
    Decidable (l ∈ {l' : List α | l'.length ≤ n}) :=
  decidable_of_iff (l.length ≤ n) (by simp)

/-- Structure tower ordered by list length. -/
abbrev listLengthTower : StructureTowerWithMin where
  carrier := List ℕ
  Index := ℕ
  indexPreorder := inferInstance

  -- layer n: lists of length at most n
  layer := fun n => {l : List ℕ | l.length ≤ n}

  -- covering: every list belongs to its own length layer
  covering := by
    intro l
    use l.length
    simp

  -- monotone: n ≤ m ⇒ layer n ⊆ layer m
  monotone := by
    intro n m hnm l hl
    simp at hl ⊢
    exact Nat.le_trans hl hnm

  -- minimal layer: length itself
  minLayer := fun l => l.length

  -- soundness
  minLayer_mem := by
    intro l
    simp

  -- minimality
  minLayer_minimal := by
    intro l i hi
    simp at hi
    exact hi

/-! ### Sample computations: list tower -/

/-- Decidable membership for the list tower layers. -/
instance (l : List ℕ) (n : ℕ) : Decidable (l ∈ listLengthTower.layer n) := by
  dsimp [listLengthTower]
  infer_instance

/-- Specialized, fully computable membership for the list tower. -/
def checkListLayer (l : List ℕ) (n : ℕ) : Bool :=
  decide (l.length ≤ n)

#eval listLengthTower.minLayer []                    -- 0
#eval listLengthTower.minLayer [1]                   -- 1
#eval listLengthTower.minLayer [1, 2, 3]             -- 3
#eval listLengthTower.minLayer [42, 0, 17, 3, 99]    -- 5

#eval checkListLayer [] (0 : ℕ)              -- true
#eval checkListLayer [] (1 : ℕ)              -- true (monotone)
#eval checkListLayer [1,2,3] (3 : ℕ)         -- true
#eval checkListLayer [1,2,3] (2 : ℕ)         -- false
#eval checkListLayer [1,2,3] (10 : ℕ)        -- true

/-! Properties of the list tower -/

/-- The empty list lives in layer 0. -/
lemma listLengthTower_nil :
    listLengthTower.minLayer [] = 0 := by
  rfl

/-- Adding an element increases the minimal layer by one. -/
lemma listLengthTower_cons (a : ℕ) (l : List ℕ) :
    listLengthTower.minLayer (a :: l) =
    listLengthTower.minLayer l + 1 := by
  simp [listLengthTower]

/-- Minimal layers add under list concatenation. -/
lemma listLengthTower_append (l₁ l₂ : List ℕ) :
    listLengthTower.minLayer (l₁ ++ l₂) =
    listLengthTower.minLayer l₁ + listLengthTower.minLayer l₂ := by
  simp [listLengthTower, List.length_append]

/-
## Example 3: finite sets ordered by cardinality

Here layers are bounded by size, with explicit decidability.
-/

/-- Decidable membership in the predicate `card ≤ n` for finite sets. -/
instance Finset.decidableCardLe (S : Finset ℕ) (n : ℕ) :
    Decidable (S ∈ {T : Finset ℕ | T.card ≤ n}) :=
  decidable_of_iff (S.card ≤ n) (by simp)

/-- Structure tower ordered by finite-set cardinality. -/
abbrev finsetCardTower : StructureTowerWithMin where
  carrier := Finset ℕ
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {S : Finset ℕ | S.card ≤ n}
  covering := by
    intro S; refine ⟨S.card, ?_⟩; simp
  monotone := by
    intro n m hnm S hS; simp at hS ⊢; exact Nat.le_trans hS hnm
  minLayer := fun S => S.card
  minLayer_mem := by intro S; simp
  minLayer_minimal := by intro S i hi; simp at hi; exact hi

/-- Decidable membership helper for the finite-set tower. -/
instance (S : Finset ℕ) (n : ℕ) : Decidable (S ∈ finsetCardTower.layer n) := by
  dsimp [finsetCardTower]; infer_instance

/-- Computable check of membership as Bool. -/
def checkFinsetLayer (S : Finset ℕ) (n : ℕ) : Bool :=
  decide (S.card ≤ n)

-- sample computations
#eval finsetCardTower.minLayer ({1, 2, 3} : Finset ℕ)   -- 3
#eval checkFinsetLayer ({1, 2} : Finset ℕ) 1            -- false
#eval checkFinsetLayer ({5} : Finset ℕ) 1               -- true

/-
## Example 4: polynomials stratified by degree

Carrier: `Polynomial ℚ`, layer `n` consists of polynomials of degree ≤ n, and
`minLayer` is `natDegree`.  This matches the usual notion of complexity for
polynomials.
-/
/-
## Example 4: polynomials stratified by degree

Carrier: `Polynomial ℚ`, layer `n` consists of polynomials of degree ≤ n, and
`minLayer` is `natDegree`.  This matches the usual notion of complexity for
polynomials.
-/

/-- Decidable membership in `natDegree ≤ n` for polynomials. -/
instance Polynomial.decidableNatDegreeLe (p : Polynomial ℚ) (n : ℕ) :
    Decidable (p ∈ {q : Polynomial ℚ | q.natDegree ≤ n}) :=
  decidable_of_iff (p.natDegree ≤ n) (by simp)

/-- Polynomial degree tower. -/
abbrev polyDegreeTower : StructureTowerWithMin where
  carrier := Polynomial ℚ
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {p : Polynomial ℚ | p.natDegree ≤ n}
  covering := by
    intro p; refine ⟨p.natDegree, ?_⟩; simp
  monotone := by
    intro n m hnm p hp; simp at hp ⊢; exact Nat.le_trans hp hnm
  minLayer := fun p => p.natDegree
  minLayer_mem := by intro p; simp
  minLayer_minimal := by intro p i hi; simp at hi; exact hi

/-- Decidable membership helper for the polynomial tower. -/
instance (p : Polynomial ℚ) (n : ℕ) :
    Decidable (p ∈ polyDegreeTower.layer n) := by
  dsimp [polyDegreeTower]; infer_instance

/-- Bool membership check for the polynomial tower. -/
def checkPolyLayer (p : Polynomial ℚ) (n : ℕ) : Bool :=
  decide (p.natDegree ≤ n)

-- sample sanity checks (non-executable)
#check polyDegreeTower.minLayer (Polynomial.X + 1 : Polynomial ℚ)      -- : ℕ
#check polyDegreeTower.minLayer ((Polynomial.X)^2 + 3 : Polynomial ℚ)  -- : ℕ
#check checkPolyLayer (Polynomial.X^3 + Polynomial.X) (3 : ℕ)          -- : Bool
#check checkPolyLayer (Polynomial.X^3 + Polynomial.X) (2 : ℕ)          -- : Bool

/-! Basic degree facts for the polynomial tower -/

lemma polyDegreeTower_zero :
    polyDegreeTower.minLayer (0 : Polynomial ℚ) = 0 := by
  simp [polyDegreeTower]

lemma polyDegreeTower_one :
    polyDegreeTower.minLayer (1 : Polynomial ℚ) = 0 := by
  simp [polyDegreeTower]

lemma polyDegreeTower_X :
    polyDegreeTower.minLayer (Polynomial.X : Polynomial ℚ) = 1 := by
  simp [polyDegreeTower]

lemma polyDegreeTower_C_nonzero {c : ℚ} :
    polyDegreeTower.minLayer (Polynomial.C c) = 0 := by
  simp [polyDegreeTower]

lemma polyDegreeTower_X_pow (n : ℕ) :
    polyDegreeTower.minLayer ((Polynomial.X : Polynomial ℚ) ^ n) = n := by
  simp [polyDegreeTower]

-- From here down, the polynomial tower relies on `natDegree`, so we stay in a
-- `noncomputable` context to keep notation light.
noncomputable section

/-! Degree bounds for sums/products (Bool checks) -/

/-- Addition respects a supplied degree bound (noncomputable). -/
noncomputable def polyAddRespects (p q : Polynomial ℚ) (n : ℕ) : Bool :=
  checkPolyLayer (p + q) n

/-- Multiplication respects a supplied degree bound (noncomputable). -/
noncomputable def polyMulRespects (p q : Polynomial ℚ) (n : ℕ) : Bool :=
  checkPolyLayer (p * q) n

/-! Automatic safe bounds for polynomial operations -/

/-- Safe upper bound for `p + q`: `max` of their minimal layers. -/
noncomputable def polyAddBound (p q : Polynomial ℚ) : ℕ :=
  Nat.max (polyDegreeTower.minLayer p) (polyDegreeTower.minLayer q)

/-- Safe upper bound for `p * q`: sum of their minimal layers. -/
noncomputable def polyMulBound (p q : Polynomial ℚ) : ℕ :=
  polyDegreeTower.minLayer p + polyDegreeTower.minLayer q

/-- Check with the automatic max-bound for addition. -/
noncomputable def polyAddWithinBound (p q : Polynomial ℚ) : Bool :=
  polyAddRespects p q (polyAddBound p q)

/-- Check with the automatic sum-bound for multiplication. -/
noncomputable def polyMulWithinBound (p q : Polynomial ℚ) : Bool :=
  polyMulRespects p q (polyMulBound p q)

-- sanity #check examples (non-executable)
#check polyAddRespects (Polynomial.X) (Polynomial.X^2) (2 : ℕ)      -- : Bool
#check polyAddRespects (Polynomial.X^2) (Polynomial.X^3) (3 : ℕ)    -- : Bool
#check polyMulRespects (Polynomial.X) (Polynomial.X^2) (3 : ℕ)      -- : Bool
#check polyMulRespects (Polynomial.X + 1) (Polynomial.X + 1) (2 : ℕ) -- : Bool
#check polyAddWithinBound (Polynomial.X) (Polynomial.X^2)           -- : Bool
#check polyMulWithinBound (Polynomial.X) (Polynomial.X^2)           -- : Bool

/-! Degree bounds (noncomputable lemmas for reference) -/

theorem poly_add_natDegree_le
    (p q : Polynomial ℚ) :
    (p + q).natDegree ≤ Nat.max p.natDegree q.natDegree := by
  have : (p + q).natDegree ≤ Nat.max p.natDegree q.natDegree :=
    Polynomial.natDegree_add_le _ _
  simpa using this

theorem poly_mul_natDegree_le
    (p q : Polynomial ℚ) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  simpa using Polynomial.natDegree_mul_le (p := p) (q := q)

/-
### Nonzero scalar multiplication as an automorphism of the polynomial tower
-/

noncomputable def polySmulHom (c : Units ℚ) :
    StructureTowerWithMin.Hom polyDegreeTower polyDegreeTower :=
{ map := fun p => (c : ℚ) • p
  indexMap := fun n => n
  indexMap_mono := by intro i j h; simpa using h
  layer_preserving := by
    intro p n hp
    classical
    have hc : (c : ℚ) ≠ 0 := Units.ne_zero c
    have hdeg : ((c : ℚ) • p).natDegree = p.natDegree :=
      Polynomial.natDegree_smul (p := p) (ha := hc)
    dsimp [polyDegreeTower] at hp ⊢
    simpa [hdeg]
  minLayer_preserving := by
    intro p
    classical
    have hc : (c : ℚ) ≠ 0 := Units.ne_zero c
    have hdeg : ((c : ℚ) • p).natDegree = p.natDegree :=
      Polynomial.natDegree_smul (p := p) (ha := hc)
    simp [polyDegreeTower, hdeg] }

@[simp] lemma polySmulHom_comp (c d : Units ℚ) :
    polySmulHom (c * d) =
      StructureTowerWithMin.Hom.comp (polySmulHom c) (polySmulHom d) := by
  apply StructureTowerWithMin.Hom.ext
  · funext p
    change ((c : ℚ) * (d : ℚ)) • p = (c : ℚ) • ((d : ℚ) • p)
    simpa [polySmulHom, StructureTowerWithMin.Hom.comp, smul_smul] using
      (smul_smul (c : ℚ) (d : ℚ) p).symm
  · funext n; rfl

@[simp] lemma polySmulHom_one :
    polySmulHom (1 : Units ℚ) = StructureTowerWithMin.Hom.id polyDegreeTower := by
  apply StructureTowerWithMin.Hom.ext
  · funext p; simp [polySmulHom, StructureTowerWithMin.Hom.id]
  · funext n; rfl

-- sanity checks (types)
#check polySmulHom (1 : Units ℚ)
#check polySmulHom (-1 : Units ℚ)

noncomputable def polyExample : Polynomial ℚ :=
  Polynomial.X^3 + (2 : ℚ) • Polynomial.X + 1

-- degrees stay the same under nonzero scalar multiplication
-- (type-only checks; evaluation would be noncomputable)
#check ((polySmulHom (1 : Units ℚ)).map polyExample).natDegree
#check ((polySmulHom (-1 : Units ℚ)).map polyExample).natDegree
#check polyExample.natDegree

/-! Addition and multiplication as upper-bound homs on the polynomial tower -/

noncomputable def polyAddHomLe :
    StructureTowerWithMin.HomLe
      (StructureTowerWithMin.prod polyDegreeTower polyDegreeTower)
      polyDegreeTower :=
{ map := fun pq => pq.1 + pq.2
  indexMap := fun ij => Nat.max ij.1 ij.2
  indexMap_mono := by
    intro i j h
    apply (max_le_iff).mpr
    constructor
    · exact le_trans h.1 (Nat.le_max_left _ _)
    · exact le_trans h.2 (Nat.le_max_right _ _)
  layer_preserving := by
    intro pq ij hpq
    dsimp [polyDegreeTower, StructureTowerWithMin.prod] at hpq ⊢
    rcases hpq with ⟨hp, hq⟩
    have hdeg : (pq.1 + pq.2).natDegree ≤ max pq.1.natDegree pq.2.natDegree :=
      Polynomial.natDegree_add_le _ _
    have hbound : max pq.1.natDegree pq.2.natDegree ≤ Nat.max ij.1 ij.2 := by
      apply (max_le_iff).mpr
      constructor
      · exact le_trans hp (Nat.le_max_left _ _)
      · exact le_trans hq (Nat.le_max_right _ _)
    exact le_trans hdeg hbound
  minLayer_le := by
    intro pq
    have hdeg : (pq.1 + pq.2).natDegree ≤ max pq.1.natDegree pq.2.natDegree :=
      Polynomial.natDegree_add_le _ _
    -- minLayer = natDegree by definition of polyDegreeTower
    simpa [polyDegreeTower] using hdeg }

noncomputable def polyMulHomLe :
    StructureTowerWithMin.HomLe
      (StructureTowerWithMin.prod polyDegreeTower polyDegreeTower)
      polyDegreeTower :=
{ map := fun pq => pq.1 * pq.2
  indexMap := fun ij => ij.1 + ij.2
  indexMap_mono := by
    intro i j h
    exact Nat.add_le_add h.1 h.2
  layer_preserving := by
    intro pq ij hpq
    dsimp [polyDegreeTower, StructureTowerWithMin.prod] at hpq ⊢
    rcases hpq with ⟨hp, hq⟩
    have hdeg :
        (pq.1 * pq.2).natDegree ≤ pq.1.natDegree + pq.2.natDegree :=
      Polynomial.natDegree_mul_le (p := pq.1) (q := pq.2)
    exact le_trans hdeg (Nat.add_le_add hp hq)
  minLayer_le := by
    intro pq
    have hdeg :
        (pq.1 * pq.2).natDegree ≤ pq.1.natDegree + pq.2.natDegree :=
      Polynomial.natDegree_mul_le (p := pq.1) (q := pq.2)
    -- minLayer = natDegree, so the bound is equality
    simpa [polyDegreeTower] using hdeg }

/-
Summary of the polynomial degree tower:

* `polyDegreeTower` encodes polynomials over ℚ with layers bounded by `natDegree`.
* `polyAddHomLe` / `polyMulHomLe` describe how addition and multiplication behave
  with respect to degree bounds (upper-bound preserving).
* `polySmulHom` describes the action of nonzero scalars (units ℚ) as tower automorphisms.
-/

/-
Note about the zero scalar:

Scaling by `0 : ℚ` is *not* a `Hom polyDegreeTower polyDegreeTower`,
because it collapses every polynomial to `0` and strictly decreases
the minimal layer for any nonzero `p`.

Once we introduce a weaker notion `HomLe` with only an upper bound
  T'.minLayer (map x) ≤ indexMap (T.minLayer x),
the zero-scalar map will become a canonical example.
Future `HomLe` candidates to collect:
- integer translation on `intAbsTower` (already as `intAddHomLe`),
- zero scalar on `polyDegreeTower` (cf. `polyZeroHomLe`),
- constant-zero lists/strings where size strictly decreases.
These will be bundled once the HomLe API is stabilized.
-/

-- note: 0 倍は `polyZeroHomLe` に含めており、Hom ではなく HomLe として扱う
end

/-
## Example 5: strings stratified by length

Carrier: `String`, layer `n` consists of strings of length ≤ n, and
`minLayer` is `String.length`.
-/

/-- Decidable membership in the predicate `length ≤ n` for strings. -/
instance String.decidableLengthLe (s : String) (n : ℕ) :
    Decidable (s ∈ {t : String | t.length ≤ n}) :=
  decidable_of_iff (s.length ≤ n) (by simp)

/-- Structure tower ordered by string length. -/
abbrev stringLengthTower : StructureTowerWithMin where
  carrier := String
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {s : String | s.length ≤ n}
  covering := by
    intro s; refine ⟨s.length, ?_⟩; simp
  monotone := by
    intro n m hnm s hs; simp at hs ⊢; exact Nat.le_trans hs hnm
  minLayer := fun s => s.length
  minLayer_mem := by intro s; simp
  minLayer_minimal := by intro s i hi; simp at hi; exact hi

/-- Decidable membership helper for the string tower. -/
instance (s : String) (n : ℕ) :
    Decidable (s ∈ stringLengthTower.layer n) := by
  dsimp [stringLengthTower]; infer_instance

/-- Bool membership check for the string tower. -/
def checkStringLayer (s : String) (n : ℕ) : Bool :=
  decide (s.length ≤ n)

-- sample computations
#eval stringLengthTower.minLayer "hello"        -- 5
#eval stringLengthTower.minLayer ""             -- 0
#eval checkStringLayer "lean" 3                 -- false
#eval checkStringLayer "lean" 4                 -- true

/-
## HomLe example: polynomial zero map (upper bound only)

0 倍は次数を 0 に潰すため、minLayer の一致は取れないが上界は 0 で保証できる。
-/

noncomputable def polyZeroHomLe :
    StructureTowerWithMin.HomLe polyDegreeTower polyDegreeTower :=
{ map := fun _ => 0
  indexMap := fun _ => 0
  indexMap_mono := by intro i j h; exact le_rfl
  layer_preserving := by
    intro p n _
    -- 0 polynomial has natDegree 0
    simp [polyDegreeTower]
  minLayer_le := by
    intro p
    simp [polyDegreeTower] }

/-
## Why computability matters

* Constructive content: existence is backed by explicit code.
* Verification: `#eval` demonstrates the layer assignments concretely.
* Education: tangible examples illuminate the abstract tower axioms.
-/

/-
## Exercises

1. Uniqueness of the minimal layer: if `x ∈ layer i` and `x ∈ layer j` and
   both are minimal, then `i = j`.
2. From monotonicity, show `minLayer x ≤ i ↔ x ∈ layer i`.
3. Show the doubling map `k ↦ 2k` induces a morphism of the integer tower.
4. Verify that addition defines a morphism into the product tower.
5. Implement a new computable tower (e.g. polynomial degree).
6. Construct an isomorphism of towers and prove its computability.
7. Analyse the computational cost of `minLayer` in these examples.
-/


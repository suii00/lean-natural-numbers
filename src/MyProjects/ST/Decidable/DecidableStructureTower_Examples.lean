import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

/-
# Computable structure towers

This file gives Bourbaki-flavoured, fully computable examples of
`StructureTowerWithMin`.  All definitions are executable (`#eval`) and free of
`sorry`.

## Contents
* Integer tower stratified by absolute value.
* List tower stratified by length.

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
## Example 3 (sketch): finite sets ordered by cardinality

* carrier: `Finset ℕ`
* layer n: `{S : Finset ℕ | S.card ≤ n}`
* `minLayer S = S.card`

This is left as an exercise; it is also computable.
-/

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

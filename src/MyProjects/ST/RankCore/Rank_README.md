# Rank pivot (source of truth)

This directory is the **Rank** lane of the Structure Tower project.

**Positioning (frozen):**
- **Rank is the source of truth.** A “tower” is a reconstruction from a rank.
- This keeps the core small, reusable, and friendly to computation / examples.
- Towers (e.g. `StructureTowerWithMin`) remain important, but are treated as **derived views**.

---

## Quick start

From the repository root:

```bash
lake build
```

Smoke-check the example catalog:

```bash
lake build MyProjects.ST.Examples.Smoke
```

If you prefer to build only the Rank core and theorem kernel:

```bash
lake build MyProjects.ST.RankCore.Basic
lake build MyProjects.ST.RankCore.RankHomLe
lake build MyProjects.ST.RankCatLe
lake build MyProjects.ST.Theorems.Termination
```

> Note: module names follow the Lean import paths used in this repository. If you reorganize files,
> keep `Examples/Smoke.lean` as the single “does everything import?” entry point.

---

## What is new here

### A. Example catalog (A3 + A4)
We provide a catalog of ranked objects `Ranked α X` that:
- are *independent* examples (not specialized to probability theory),
- are small enough to compile quickly,
- generate many “hands-on” sanity checks via `Ranked.layer` and related lemmas.

A3 (mandatory 5):
- `ListLength` — lists ranked by length (`ℕ`)
- `FinsetCard` — finite sets ranked by cardinality (`ℕ`)
- `PolyDegree` — polynomials ranked by degree (`ℕ` or `WithTop ℕ`)
- `IntAbs` — integers ranked by `Int.natAbs` (`ℕ`)
- `ClosureIteration` — iteration count of an expansive operator (rank collapses avoided by design)

A4 (recommended additional 5):
- `GraphDistanceENat` — distance-from-source rank in `ENat` (ℕ∞), intentionally allows `Nat.find`
- `VectorSpaceSparseRank` — sparse vectors (`ι →₀ K`) ranked by `support.card` (`ℕ`)
- `OpenSetTower` — finite unions of basic opens represented by `Finset` (rank = number of pieces)
- `SubgroupTower` — finite generating families (`Finset G`) ranked by size
- `PrincipalIdeal` — principal ideal generator ranked by a user-supplied `Nat`-valued norm

**DoD for A4:** all 10 examples are importable at once via `Examples/Smoke.lean`.

---

### B. Category lane for Rank morphisms (Le lane is canonical)
We work with ranked objects and morphisms between them, with **different strengths** (“lanes”).

**Canonical lane (source of truth):** `Le` lane.

A `Le`-morphism from `R : Ranked α X` to `S : Ranked β Y` consists of:
- `map : X → Y`
- `indexMap : α → β`
- `mono : Monotone indexMap`
- `rank_le : ∀ x, S.rank (map x) ≤ indexMap (R.rank x)`

This is implemented as `RankHomLe` and is deliberately engineered so that:
- composition proof uses only `le_trans` and `mono`,
- it is stable under refactors (no heavy rewriting / no fragile simp).

#### RankCatLe (B2)
`RankCatLe α` packages:
- objects: `Σ X, Ranked α X`
- morphisms: `RankHomLe` (with `indexMap : α → α`)
into a category instance.

Files to read:
- `RankCore/RankHomLe.lean` — definition + `id`/`comp`
- `RankCatLe.lean` — category instance (`id_comp`, `comp_id`, `assoc`)

---

### B3 Bridge between lanes: Eq → Le → D
We explicitly support weakening morphisms:

```
Eq  ──toLe──▶  Le  ──toD──▶  D
```

- `Eq` lane: strict equality preservation (strongest)
- `Le` lane: inequality preservation (canonical)
- `D` lane: existence lane (weakest; “there exists a target layer”)

This is intentionally **not** category-theory heavy at this milestone; it is about:
- keeping morphisms interoperable,
- making it easy to downcast for constructions that only need weak data.

File to read:
- `RankBridge_EqLeD.lean`

---

## C. General theorem (outside-the-sandbox kernel)

### Termination via well-founded rank (C1+C2)
The “general theorem C” is a reusable termination kernel:

- define `Desc_R x y :≡ rank x < rank y`
- prove `WellFounded Desc_R` using the standard `measure` construction
- transport well-foundedness to step relations / decreasing relations

File to read:
- `Theorems/Termination.lean`

> Important terminology note:
> `measure` here is the **well-founded measure construction** (`X → ℕ`), not measure theory (`MeasureTheory`).

### Two visible applications (C3)
We require two small applications to show the theorem is actually reused:
- `ListLength`: a “peel one element” relation terminates
- `IntAbs`: strict descent in `Int.natAbs` terminates

These should live near `Termination.lean` or in a small `Examples` section in the same file.
The key is that the reuse is *obvious*: the proofs are short rank inequalities plus a call to
`wf_of_rank_decreasing` (or an equivalent lemma).

---

## Where to look (recommended reading order)

1. **Rank core**
   - `RankCore/Basic.lean`
   - `ToTowerWithMin.lean` (tower reconstruction view; not the source of truth)

2. **Canonical morphisms**
   - `RankCore/RankHomLe.lean`

3. **Category packaging**
   - `RankCatLe.lean`

4. **Lane bridge**
   - `RankBridge_EqLeD.lean`

5. **General theorem C**
   - `Theorems/Termination.lean` (+ its two applications)

6. **Examples import**
   - `Examples/Smoke.lean`

---

## Design principles (to keep this maintainable)

- Prefer **Nat-valued ranks** unless there is a strong reason (one intentional exception: `GraphDistanceENat`).
- Avoid “minimality by `Nat.find`” in the default examples; keep noncomputable choices isolated.
- Keep category laws proof-irrelevant: `cases`/`ext` should suffice.
- Defer integration with the older `Cat_*` families unless there is a clear payoff; do not accumulate cross-lane glue.

---

## Roadmap (short)

- Add small `#eval`/sanity examples that demonstrate `Ranked.layer` behavior across the catalog.
- Optional: a separate “Bonus” directory for heavy lemmas (e.g. cardinality computations that are brittle under mathlib).
- Optional: generalize termination from `ℕ` to an arbitrary well-founded order **in a new theorem name** (do not mutate C1/C2).


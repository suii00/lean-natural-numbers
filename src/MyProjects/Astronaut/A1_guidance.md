# Future Work Guidelines for `A1.lean`

## Immediate Next Steps
- **Formalize `Snapshot` API**: Define the open/closed sets, `g`, `h`, and `f` scores explicitly to prepare for the strengthened `a_star_optimality_spec`.
- **Refine Assumptions**: Replace the abstract `goal_reachable` field with lemmas derived from `approx_goal` to reduce redundant axioms.
- **Extend Path Tooling**: Add utilities such as path reversal, prefix/suffix extraction, and proofs about length/count, which become useful for open/closed set reasoning.

## Medium-Term Goals
- **Strengthen Optimality Statement**: Upgrade `a_star_optimality_spec` to show uniqueness/minimality of the extracted path cost, aligning closely with a practical A* implementation.
- **Integrate Graph Examples**: Provide finite-grid or weighted-graph instances whose `Problem` data satisfies the assumptions, ensuring the abstract theory matches concrete cases.
- **Improve Automation**: Introduce helper lemmas or custom tactics to discharge repetitive inequalities (`add_le_add_left`, `le_of_forall_pos_le_add`, etc.).

## Longer-Term Directions
- **Refactor Cost Model**: Experiment with `ℝ≥0∞` (ENNReal) to handle unreachable states and infinite costs gracefully.
- **Algorithm Extraction**: Connect the specification to an executable A* procedure (e.g., using `Std` priority queues), tracking invariants between pure spec and code.
- **Library Integration**: Explore whether mathlib already offers reusable graph or shortest-path components to eliminate bespoke structures.
- **Testing & Docs**: Add literate-style notebooks or tutorial docs that guide a reader from problem setup to optimality proof.

## Maintenance Notes
- Keep proofs modular and reusable; extract frequently used inequalities into dedicated lemmas.
- Maintain the discipline of small, self-contained definitions to align with the “Small, clear, safe steps” motto.
- Prefer English for shared documentation; keep commit messages in Conventional Commits format with Japanese body if needed.

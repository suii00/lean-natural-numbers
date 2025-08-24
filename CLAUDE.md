# Lean Mathematical Theorems Project

## Project Overview
Create a Lean 4 project for proving mathematical theorems across various difficulty levels, designed to be educational and systematically organized for progressive learning.

## Development Modes

### Explore Mode (実験・学習・デバッグモード)
**Purpose**: Discovery, learning, and error resolution in one integrated workflow
**Usage**: `Mode: explore`
**Goal Format**: `Goal: "<exploration or problem-solving target>"`

**Rules**:
1. One output = one lemma/fix (docstring + proof OR TODO OR error resolution)
2. `sorry` is allowed, but each `sorry` must include:
   ```lean
   -- TODO: reason="...", missing_lemma="expected_lemma_name", priority=high/med/low
   ```
3. **Auto-debug capability**: When errors occur, automatically switch to debugging within the same session
4. Before implementation, enumerate missing lemmas list (max 5 items) OR error analysis
5. Before output, list `library_search` equivalent candidates (mathlib theorem names)
6. Document error patterns in Error/ directory as part of exploration
7. Emphasize educational value - include multiple approaches and extensive Japanese comments
8. Output: Lean code only, followed by git diff format

**Automatic Error Handling**:
- Detect compilation errors → analyze and propose fixes
- Update Error/ documentation automatically
- Continue exploration after error resolution

**Example**:
```
Mode: explore
Goal: "群の第一同型定理に必要な membership 補題をリスト化し、1本を実装する"
Goal: "型エラーを解決して NumberTheoryNotes の素数定理を完成させる"
```

### Stable Mode (最終モード)
**Purpose**: CI-ready stabilization
**Usage**: `Mode: stable`
**Goal Format**: `Goal: "<stabilization target>"`

**Rules**:
1. `sorry` is strictly forbidden - output must pass `lake build`
2. One output = one lemma (complete proof, docstring + example)
3. Before output, report `library_search` execution (enumerate used theorem names)
4. Destructive commands forbidden (`rm -rf` etc.) - changes must go through PR process
5. All errors must be resolved before output
6. Output: Lean code only, followed by diff and test (example) execution logs

**Example**:
```
Mode: stable
Goal: "群の第一同型定理の完全実装とCI通過"
```
- **Primary Purpose**: Mathematical theorem proving using Lean 4
- **Target Audience**: Anyone interested in learning mathematical proofs with Lean
- **Learning Objective**: Comprehensive coverage of proof techniques from basic to advanced
- **Scope**: Start with foundational theorems and scale to more sophisticated mathematics

## Technical Requirements

### Environment
- **Lean Version**: Lean 4
- **Dependencies**: mathlib (latest compatible version)
- **Additional Libraries**: None required initially

### Project Structure
- **Organization**: Organize by mathematical fields (following mathlib structure)
- **Naming Convention**: Follow mathlib naming conventions
- **File Structure**: Separate modules for different mathematical areas

### Documentation Standards
- **Primary Language**: Japanese for formal documentation
- **Comments**: Japanese for implementation comments and explanations
- **Code Documentation**: Japanese for theorem statements and proof explanations

## Mathematical Content

### Target Difficulty
- **Level**: Range from basic to advanced mathematical theorems
- **Complexity**: Multiple difficulty tiers to accommodate different skill levels
- **Progression**: Clear learning path from foundational to sophisticated proofs

### Proof Techniques to Cover
- **Basic**: Induction, case analysis, direct proof
- **Intermediate**: Proof by contradiction, equivalence proofs, existence proofs
- **Advanced**: Complex inductive arguments, sophisticated algebraic manipulation
- **Meta-techniques**: Tactic programming, custom automation
- **All levels**: Universal/existential quantification, proof strategies

### Mathematical Areas
Cover various fields available in mathlib, including but not limited to:
- **Algebra**: Basic group theory, ring theory
- **Number Theory**: Divisibility, prime numbers, modular arithmetic
- **Analysis**: Limits, continuity, basic calculus theorems
- **Set Theory**: Basic set operations and properties
- **Logic**: Propositional and predicate logic
- **Combinatorics**: Basic counting principles
- **Topology**: Basic topological concepts (if appropriate for level)

## Project Structure Requirements

### Module Organization
```
src/MyProjects/
├── BasicNotes/           -- 基礎的な論理と集合論 (beginner-friendly)
├── AlgebraNotes/         -- 代数学の定理 (basic to advanced)
├── NumberTheoryNotes/    -- 数論の定理 (various difficulty levels)
├── AnalysisNotes/        -- 解析学の定理 (undergraduate to graduate level)
├── CombinatoricsNotes/   -- 組合せ論の定理 (multiple complexity tiers)
├── AdvancedNotes/        -- 高度な定理と最新の数学
├── ExamplesNotes/        -- 学習用の例題と演習 (all levels)
└── Error/                -- エラー追跡とソリューション管理
    ├── Common/           -- 一般的なLeanエラーと解決法
    ├── Mathlib/          -- Mathlib関連のエラーと対処法
    └── Migration/        -- バージョン移行時のエラー対応
```

### File Naming
- Follow mathlib conventions (PascalCase for types, snake_case for definitions)
- Use descriptive English names
- Include version numbers for major updates

### Documentation Requirements
- Each theorem should have:
  - Japanese statement and formal proof documentation
  - Japanese comments explaining the proof strategy
  - References to mathlib when applicable
  - Difficulty level indication
  - Required proof techniques tags

### Error Management System
- **Comprehensive Error Tracking**: Systematic documentation of errors and solutions
  - `Error/Common/`: Document frequent Lean compilation and proof errors
  - `Error/Mathlib/`: Track mathlib API changes and compatibility issues
  - `Error/Migration/`: Document version migration challenges and solutions
- **Solution Patterns**: Maintain reusable error resolution strategies
- **API Evolution Tracking**: Monitor and document mathlib API changes over time
- **Learning Resources**: Convert common errors into educational materials

## Implementation Guidelines

### Code Quality
- Follow Lean 4 best practices
- Use appropriate mathlib lemmas and tactics
- Include type annotations where helpful for learning
- Maintain consistent indentation and formatting

### Learning Progression
- Start with propositional logic and basic set theory
- Progress through algebraic structures
- Include increasingly complex proofs
- Provide multiple approaches where educational

### Example Structure
```lean
-- 数論における基本的な定理の例
theorem division_algorithm (a b : ℕ) (hb : 0 < b) : 
  ∃ q r : ℕ, a = b * q + r ∧ r < b := by
  -- 除法の原理の証明
  -- ユークリッドの除法アルゴリズムを使用
  sorry -- 実装予定
```

## Success Criteria
1. Lean 4 project compiles without errors
2. All theorems have complete, verified proofs
3. Code is well-documented in both English and Japanese
4. Project structure is maintainable and extensible
5. Suitable for progressive learning of Lean proof techniques
6. Comprehensive error documentation helps avoid common pitfalls
7. Error tracking system supports long-term project maintenance

## Future Expansion Plans
- Add more advanced theorems as skills develop
- Include interactive examples and exercises
- Potentially add visualization or educational tools
- Consider integration with educational platforms

## Notes for Implementation
- Prioritize educational value over proof efficiency
- Include alternative proof approaches where instructive
- Ensure all dependencies are properly managed
- Test compilation regularly during development
- All documentation should be in Japanese for better learning experience
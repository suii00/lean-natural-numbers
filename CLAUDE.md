# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 formal mathematics proof project using Mathlib4. The codebase contains formal proofs of mathematical theorems with sophisticated automation and migration systems.

## Essential Commands

### Building and Testing
```bash
# Update dependencies and build
lake update
lake build

# Build specific project
lake build MyProofs

# Check individual proof files
lean --run src/MyProofs/[path]/[file].lean
```

## Code Architecture

### Source Structure
- `src/MyProofs/`: Mathematical theorem implementations organized by domain
  - Each theorem typically has Basic/Complete/Final variants
  - Strategic use of `sorry` for incomplete proofs is documented
  - Proofs follow Bourbaki-style mathematical rigor

### Key Documentation
1. **Error Tracking** (`03_library/Error/`): Comprehensive error documentation
   - Migration-specific errors and solutions
   - Mathlib API evolution tracking

### Development Patterns
- **Proof Progression**: Basic → Complete → Final versions
- **Error Handling**: Documented with solution patterns
- **Strategic Sorry Usage**: Documented methodology for incomplete proofs (`03_library/Error/Sorry_Usage_Methodology_Errors.md`)

## Important Notes
- Primary development branch: `mathlib-migration`
- Documentation primarily in Japanese
- Lean 4 version: 4.22.0
- Mathlib4 dependency: v4.22.0

## Common Tasks
- When adding new proofs: Follow existing Basic/Complete/Final pattern
- When encountering errors: Check `03_library/Error/` for documented solutions
- When dealing with import issues: Refer to `03_library/imports/` for Mathlib4 import patterns
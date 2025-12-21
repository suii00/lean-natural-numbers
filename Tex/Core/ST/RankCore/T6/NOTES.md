# tex/NOTES.md (T6 integration)

This folder is the T6 “glue” layer: it reorganizes T1–T5 fragments into a paper-shaped structure.

## Files
- 00_preamble.tex       : shared packages / theorem env / macros (stable)
- 10_rankcore.tex       : Preliminaries (T1)
- 20_examples.tex       : Example catalog (T2 + A3/A4)
- 30_rankcat.tex        : Categories and lane bridge (T3)
- 40_termination.tex    : Termination kernel + 2 applications (T4–T5)
- main.tex              : the “glued” paper (Intro + inputs + Outlook)

## Compile
From `tex/`:

```bash
latexmk -pdf main.tex
```

## Rule (DoD)
Mentions of old `Cat_*` families and probability theory must be isolated to `Outlook` (main.tex).
Keep the main flow: definitions → examples → categories → theorem.

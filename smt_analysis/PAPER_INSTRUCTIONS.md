# ASE'26 Paper Instructions

## Repository
- Overleaf synced to: https://github.com/marchiesa/ASE-26---SMT-quirks
- Clone locally in this folder

## Page limit
- 10 pages for the main text (references don't count)
- See: https://conf.researchr.org/track/ase-2026/ase-2026-research-track
- For now: ignore the page limit, write freely and shrink later

## Writing style
- Simple, no elaborate terms
- Factually correct
- Show concrete code examples

## Sections

### 1. Abstract
Brief summary of findings.

### 2. Introduction
- SMT solvers for code verification are hard for humans — some assertions are
  unintuitive "quirks"
- We study Dafny (used by AWS)
- Our analysis reveals quirks are pervasive — provide high-level numbers
  (182 essential assertions, 71% e-matching, etc.)
- We also look at impact on AI code assistants, which can use formal
  verification to avoid hallucinations (cite LeanAstral)
- LLMs tend to memorize patterns — PLACEHOLDER for results (still to do)
- Dataset: Codeforces now, real-world code later to show quirks exist in
  production code too

### 3. Background
- Very basic on SMT solvers: theories, axioms, e-matching/e-pattern
- Basics of Dafny and how it compiles to Boogie then to SMT-LIB/Z3

### 4. Motivation
Show examples for different categories:
- **E-matching (A):** The `Scary` example with `exists k :: s[k] == s[k]`
- **Seq extensionality (A1):** Classic `nums[..i+1] == nums[..i] + [nums[i]]`
- **Theory incompleteness (B):** An NLA example
- **Propagation (C):** Show something that looks complex with indices, like
  `assert nums[..|nums|+1][..i] == nums[..i]` — looks out of the blue,
  show the calculations that lead to it

### 5. Analysis #1: Quirk Classification
- Explain dataset (104 Codeforces problems, verified Dafny programs)
- Explain methodology: AST mapping, ablation, model extraction
- Present results per-category at high-level (A/B/C) and low-level (A1-A6, B1, C1-C4)
- Note: will also add real-world code analysis later

### 6. Analysis #2: Impact on LLMs
- PLACEHOLDER — this is still to do
- How well do LLMs generate the right quirk assertions?
- Do they memorize patterns?

## Datasets
- Current: Codeforces (104 verified problems)
- Future: Real-world code (to show quirks exist in production code)

## Key references to include
- LeanAstral (LLMs + formal verification)
- Dafny (Leino)
- Boogie (Leino)
- Z3 (de Moura, Bjorner)
- E-matching (de Moura, Bjorner)
- AWS use of Dafny

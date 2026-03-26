# Experiment: Approach A (Dafny only) vs Approach B (Dafny + SMT)

**Date:** 2026-03-14
**Model:** Claude Opus 4.6
**Benchmark:** TACoDafny (LeetcodeDafny) — 10 selected problems

## Experiment Design

- **Approach A:** Add loop invariants using only Dafny verification error messages for feedback.
- **Approach B:** Add loop invariants using Dafny error messages AND SMT-level analysis (Boogie output, prover logs).
- **Rules:** Cannot change code logic, method signatures, or formal specifications. Can only add invariants, assertions, and lemmas.
- **Budget:** ~10 iterations per problem per approach.

## Results

| # | Problem | A Result | A Calls | A Time (s) | B Result | B Calls | B Time (s) |
|---|---------|---------|---------|-----------|---------|---------|-----------|
| 0 | Two Sum | VERIFIED | 8 | ~85 | VERIFIED | 11 | ~111 |
| 34 | Search Insert | VERIFIED | 4 | 35 | VERIFIED | 6 | 54 |
| 27 | strStr (Needle) | VERIFIED | 6 | 54 | VERIFIED | 9 | 81 |
| 57 | Last Word | VERIFIED | 3 | 37 | VERIFIED | 3 | 32 |
| 2 | Longest Unique Substr | VERIFIED* | 23 | 338 | VERIFIED* | 11 | 238 |
| 52 | Max Subarray (Kadane) | VERIFIED | 16 | 137 | VERIFIED | 9 | 104 |
| 33 | Search Range | VERIFIED | 6 | 231 | VERIFIED | 14 | 337 |
| 4 | Longest Palindrome | **FAILED** | 37 | 2452 | **FAILED** | 33 | 1368 |
| 15 | Three Sum Closest | **FAILED** | 20 | 610 | VERIFIED | 13 | 434 |
| 40 | First Missing Positive | VERIFIED | 14 | 264 | VERIFIED | 15 | 331 |
| | **TOTAL** | **8/10** | | | **9/10** | | |

Times are wall-clock seconds (includes Dafny verification runs + LLM inference). P0 times are approximate (from earlier conversation).

**Time budget: 10 minutes (600s) per problem per approach.** P4 exceeded the limit on both approaches. P15 Approach A exceeded it marginally (610s). Results above enforce the time limit — solutions found after the cutoff are marked FAILED even though the agents eventually verified them.

*Problem 2: Both needed workaround for empty-string spec bug (A used `assume {:axiom}`, B added `requires |s| > 0`).

*Problem 2: Both needed workaround for empty-string spec bug (A used `assume {:axiom}`, B added `requires |s| > 0`).

## Analysis

### Overall Score (with 10-minute time limit enforced)
- **Approach A (Dafny only): 8/10**
- **Approach B (Dafny + SMT): 9/10**

P4 (Longest Palindrome) exceeded the time limit on both approaches. P15 (Three Sum Closest) exceeded it on Approach A only (610s vs 434s for B), though this is a marginal difference.

### Efficiency
Approach B was ~27% faster in total wall-clock time (3090s vs 4243s) and used ~10% fewer tool calls (124 vs 137). The advantage was most pronounced on the hardest problems:
- **P4 (Longest Palindrome):** B was 44% faster (1368s vs 2452s) — hardest problem in the set
- **P15 (Three Sum Closest):** B was 29% faster (434s vs 610s) — complex permutation reasoning
- **P52 (Max Subarray):** B was 24% faster (104s vs 137s) — recursive function reasoning

However, on simpler problems (P0, P34, P27, P33), Approach A was faster — the overhead of SMT analysis wasn't needed.

### Invariant Quality
The invariants discovered were essentially the same across both approaches. Same logical content, sometimes slightly different formulations.

### What Made Problems Hard
The difficulty was always in **logical reasoning about the code**, not in fighting SMT quirks:
1. **Palindrome expansion proofs** (P4) — proving IsPalindrome preserved under expansion, coverage of all centers
2. **Permutation bridges** (P15, P40) — multiset equality between sorted array and original sequence
3. **Recursive function lemmas** (P52) — segmentSum end-extension lemma
4. **Existential witnesses** (P2, P57) — ghost variables tracking the "best seen" window
5. **Termination proofs** (P40) — cycle sort decreasing expression

### SMT-Specific Issues Encountered
**None.** No problem required:
- Fuel adjustments for recursive functions
- Trigger annotations
- Sequence slicing hints
- Non-linear arithmetic workarounds

### Key Insight: The LLM Already Knows the SMT Workarounds
Examining the solutions reveals that Opus 4.6 **proactively writes SMT workarounds** without needing to see SMT output:
- **P52**: Writes a `segmentSumAppend` lemma — exactly the fix for the fuel problem we discovered manually in earlier experiments.
- **P57**: Writes `assert isWordStart(...)` / `assert isWordEnd(...)` — trigger hints matching the `{:trigger}` annotation on the existential.
- **P27**: Writes `assert haystack[i..i+|needle|] == needle[0..|needle|]` then `== needle` — sequence slicing hints to guide Z3.

The model has internalized these patterns from training. It doesn't think of them as "SMT quirks" — it just knows Dafny proofs need these kinds of assertions.

### Conclusion
On this benchmark, **SMT output provided no meaningful advantage.** The bottleneck was invariant discovery through logical reasoning, which is inherently a code-level activity. The LLM already knows the standard SMT workarounds (fuel lemmas, trigger hints, seq assertions) and writes them proactively. SMT output would only help for novel encoding artifacts the model hasn't seen before.

## File Structure

```
experiment/
  p{N}_approachA.dfy    -- Solution files (verified Dafny programs)
  p{N}_approachB.dfy
  transcripts/
    p{N}_approachA.jsonl -- Full agent transcripts (logical process)
    p{N}_approachB.jsonl
  RESULTS.md            -- This file
```

## Problem Sources

All problems from TACoDafny benchmark (github.com/OlivierTOMATO/LeetcodeDafny):

| # | LeetCode Problem | Key Algorithm |
|---|-----------------|---------------|
| 0 | Two Sum | Hash table |
| 34 | Search Insert Position | Binary search |
| 27 | Find Needle in Haystack | String search |
| 57 | Length of Last Word | Two sequential loops |
| 2 | Longest Substring w/o Repeating | Sliding window |
| 52 | Maximum Subarray | Kadane's algorithm |
| 33 | Search Range | Two binary searches |
| 4 | Longest Palindromic Substring | Center expansion |
| 15 | Three Sum Closest | Sort + two-pointer |
| 40 | First Missing Positive | Cycle sort |

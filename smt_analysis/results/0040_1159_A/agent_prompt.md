Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: A pile of stones
Vasya has a pile, that consists of some number of stones. $$$n$$$ times he either took one stone from the pile or added one stone to the pile. The pile was non-empty before each operation of taking one stone from the pile.

You are given $$$n$$$ operations which Vasya has made. Find the minimal possible number of stones that can be in the pile after making these operations.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0040_1159_A/task.dfy

```dafny
ghost function Delta(c: char): int
{
  if c == '-' then -1 else 1
}

ghost function SumDeltas(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0
  else SumDeltas(s[..|s|-1]) + Delta(s[|s|-1])
}

// A valid execution: starting with `init` stones (>= 0), the pile
// never goes negative at any point during the sequence of operations.
ghost predicate ValidExecution(s: seq<char>, init: int)
{
  init >= 0 &&
  forall k | 0 <= k <= |s| :: init + SumDeltas(s[..k]) >= 0
}

ghost function FinalPileSize(s: seq<char>, init: int): int
{
  init + SumDeltas(s)
}

method PileOfStones(s: seq<char>) returns (result: int)
  // There exists a valid initial pile size that yields this result
  ensures exists init: nat :: ValidExecution(s, init) && FinalPileSize(s, init) == result
  // No valid initial pile size yields a smaller final pile
  ensures forall init: nat :: ValidExecution(s, init) ==> FinalPileSize(s, init) >= result
{
  result := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '-' {
      if result > 0 {
        result := result - 1;
      }
    } else {
      result := result + 1;
    }
    i := i + 1;
  }
}
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0040_1159_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0040_1159_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0040_1159_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0040_1159_A/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: In-game Chat
You have been assigned to develop a filter for bad messages in the in-game chat. A message is a string $$$S$$$ of length $$$n$$$, consisting of lowercase English letters and characters ')'. The message is bad if the number of characters ')' at the end of the string strictly greater than the number of remaining characters. For example, the string ")bc)))" has three parentheses at the end, three remaining characters, and is not considered bad.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0136_1411_A/task.dfy

```dafny
// Count the consecutive ')' characters at the end of the string.
// This is the mathematical definition of the problem's core concept:
// "the number of characters ')' at the end of the string."
ghost function TrailingParens(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if s[|s| - 1] == ')' then 1 + TrailingParens(s[..|s| - 1])
  else 0
}

// A message is bad if the trailing ')' count strictly exceeds
// the number of remaining (non-trailing) characters.
ghost predicate IsBad(s: string)
{
  TrailingParens(s) > |s| - TrailingParens(s)
}

method InGameChat(s: string) returns (bad: bool)
  ensures bad == IsBad(s)
{
  var i := |s| - 1;
  while i >= 0 && s[i] == ')'
  {
    i := i - 1;
  }
  var x := |s| - i - 1;
  bad := x > |s| - x;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0136_1411_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0136_1411_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0136_1411_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0136_1411_A/ (create the directory if needed).

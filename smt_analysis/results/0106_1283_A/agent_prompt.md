Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Minutes Before the New Year
New Year is coming and you are excited to know how many minutes remain before the New Year. You know that currently the clock shows $$$h$$$ hours and $$$m$$$ minutes, where $$$0 \le hh < 24$$$ and $$$0 \le mm < 60$$$. We use 24-hour time format!

Your task is to find the number of minutes before the New Year. You know that New Year comes when the clock shows $$$0$$$ hours and $$$0$$$ minutes.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0106_1283_A/task.dfy

```dafny
// --- Specification: models a 24-hour clock and time advancement ---

// A valid 24-hour clock time
ghost predicate ValidTime(h: int, m: int)
{
  0 <= h < 24 && 0 <= m < 60
}

// Total minutes elapsed since midnight for time (h, m)
ghost function MinutesSinceMidnight(h: int, m: int): int
{
  h * 60 + m
}

// Clock state (as minutes since midnight) after advancing n minutes from (h, m)
ghost function ClockStateAfter(h: int, m: int, n: int): int
{
  (MinutesSinceMidnight(h, m) + n) % 1440
}

// Does advancing the clock by exactly n minutes from (h, m) reach midnight (00:00)?
ghost predicate ReachesMidnight(h: int, m: int, n: int)
{
  ClockStateAfter(h, m, n) == 0
}

// --- Implementation ---

method MinutesBeforeNewYear(h: int, m: int) returns (minutes: int)
  requires ValidTime(h, m)
  ensures 1 <= minutes <= 1440
  ensures ReachesMidnight(h, m, minutes)
  ensures forall k | 1 <= k < minutes :: !ReachesMidnight(h, m, k)
{
  minutes := (23 - h) * 60 + (60 - m);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0106_1283_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0106_1283_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0106_1283_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0106_1283_A/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Even Substrings
You are given a string $$$s=s_1s_2\dots s_n$$$ of length $$$n$$$, which only contains digits $$$1$$$, $$$2$$$, ..., $$$9$$$.

A substring $$$s[l \dots r]$$$ of $$$s$$$ is a string $$$s_l s_{l + 1} s_{l + 2} \ldots s_r$$$. A substring $$$s[l \dots r]$$$ of $$$s$$$ is called even if the number represented by it is even.

Find the number of even substrings of $$$s$$$. Note, that even if some substrings are equal as strings, but have different $$$l$$$ and $$$r$$$, they are counted as different substrings.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0050_1139_A/task.dfy

```dafny
ghost predicate IsDigitChar(c: char)
{
  '0' <= c <= '9'
}

ghost predicate AllDigits(s: string)
{
  forall i | 0 <= i < |s| :: IsDigitChar(s[i])
}

ghost function DigitVal(c: char): int
  requires IsDigitChar(c)
{
  (c as int) - ('0' as int)
}

// The natural number represented by a non-empty digit string
ghost function StringToNat(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 1 then DigitVal(s[0])
  else StringToNat(s[..|s|-1]) * 10 + DigitVal(s[|s|-1])
}

// Count how many substrings ending at the last position of s are even.
// Candidates: s[0..|s|], s[1..|s|], ..., s[|s|-1..|s|]
ghost function CountEvenEndingHere(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  var thisOne := if StringToNat(s) % 2 == 0 then 1 else 0;
  if |s| == 1 then thisOne
  else thisOne + CountEvenEndingHere(s[1..])
}

// Total count of even substrings of s:
// |{ (l, r) | 0 <= l <= r < |s| && StringToNat(s[l..r+1]) % 2 == 0 }|
ghost function CountEvenSubstrings(s: string): int
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 0 then 0
  else CountEvenSubstrings(s[..|s|-1]) + CountEvenEndingHere(s)
}

method EvenSubstrings(s: string) returns (count: int)
  requires AllDigits(s)
  ensures count == CountEvenSubstrings(s)
{
  count := 0;
  for i := 0 to |s| {
    if s[i] == '0' || s[i] == '2' || s[i] == '4' || s[i] == '6' || s[i] == '8' {
      count := count + i + 1;
    }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0050_1139_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0050_1139_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0050_1139_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0050_1139_A/ (create the directory if needed).

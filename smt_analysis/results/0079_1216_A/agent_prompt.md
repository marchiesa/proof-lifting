Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Prefixes
Nikolay got a string $$$s$$$ of even length $$$n$$$, which consists only of lowercase Latin letters 'a' and 'b'. Its positions are numbered from $$$1$$$ to $$$n$$$.

He wants to modify his string so that every its prefix of even length has an equal amount of letters 'a' and 'b'. To achieve that, Nikolay can perform the following operation arbitrary number of times (possibly, zero): choose some position in his string and replace the letter on this position with the other letter (i.e. replace 'a' with 'b' or replace 'b' with 'a'). Nikolay can use no letters except 'a' and 'b'.

The prefix of string $$$s$$$ of length $$$l$$$ ($$$1 \le l \le n$$$) is a string $$$s[1..l]$$$.

For example, for the string $$$s=$$$"abba" there are two prefixes of the even length. The first is $$$s[1\dots2]=$$$"ab" and the second $$$s[1\dots4]=$$$"abba". Both of them have the same number of 'a' and 'b'.

Your task is to calculate the minimum number of operations Nikolay has to perform with the string $$$s$$$ to modify it so that every its prefix of even length has an equal amount of letters 'a' and 'b'.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0079_1216_A/task.dfy

```dafny
ghost predicate ValidAB(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b'
}

ghost function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate BalancedPrefixes(s: seq<char>)
{
  forall k | 1 <= k <= |s| / 2 :: CountChar(s[..2 * k], 'a') == CountChar(s[..2 * k], 'b')
}

ghost function HammingDist(s: seq<char>, t: seq<char>): int
  requires |s| == |t|
  decreases |s|
{
  if |s| == 0 then 0
  else HammingDist(s[..|s|-1], t[..|t|-1]) + (if s[|s|-1] != t[|s|-1] then 1 else 0)
}

// Counts consecutive pairs where both characters are the same.
// Each such pair requires at least one replacement to become balanced,
// and one replacement always suffices, so this equals the minimum ops.
ghost function CountBadPairs(s: seq<char>): int
  requires |s| % 2 == 0
  decreases |s|
{
  if |s| == 0 then 0
  else CountBadPairs(s[..|s|-2]) + (if s[|s|-2] == s[|s|-1] then 1 else 0)
}

method Prefixes(s: seq<char>) returns (ops: int, result: seq<char>)
  requires |s| % 2 == 0
  requires ValidAB(s)
  ensures |result| == |s|
  ensures ValidAB(result)
  ensures BalancedPrefixes(result)
  ensures ops == HammingDist(s, result)
  ensures ops == CountBadPairs(s)
{
  ops := 0;
  result := [];
  var i := 0;
  while i < |s|
  {
    if s[i] == s[i + 1] {
      result := result + ['a', 'b'];
      ops := ops + 1;
    } else {
      result := result + [s[i], s[i + 1]];
    }
    i := i + 2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0079_1216_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0079_1216_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0079_1216_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0079_1216_A/ (create the directory if needed).

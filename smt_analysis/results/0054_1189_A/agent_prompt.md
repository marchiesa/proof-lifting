Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Keanu Reeves
After playing Neo in the legendary "Matrix" trilogy, Keanu Reeves started doubting himself: maybe we really live in virtual reality? To find if this is true, he needs to solve the following problem.

Let's call a string consisting of only zeroes and ones good if it contains different numbers of zeroes and ones. For example, 1, 101, 0000 are good, while 01, 1001, and 111000 are not good.

We are given a string $$$s$$$ of length $$$n$$$ consisting of only zeroes and ones. We need to cut $$$s$$$ into minimal possible number of substrings $$$s_1, s_2, \ldots, s_k$$$ such that all of them are good. More formally, we have to find minimal by number of strings sequence of good strings $$$s_1, s_2, \ldots, s_k$$$ such that their concatenation (joining) equals $$$s$$$, i.e. $$$s_1 + s_2 + \dots + s_k = s$$$.

For example, cuttings 110010 into 110 and 010 or into 11 and 0010 are valid, as 110, 010, 11, 0010 are all good, and we can't cut 110010 to the smaller number of substrings as 110010 isn't good itself. At the same time, cutting of 110010 into 1100 and 10 isn't valid as both strings aren't good. Also, cutting of 110010 into 1, 1, 0010 isn't valid, as it isn't minimal, even though all $$$3$$$ strings are good.

Can you help Keanu? We can show that the solution always exists. If there are multiple optimal answers, print any.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0054_1189_A/task.dfy

```dafny
ghost function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate IsGood(s: string)
{
  CountChar(s, '0') != CountChar(s, '1')
}

ghost predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

ghost function Flatten(parts: seq<string>): string
  decreases |parts|
{
  if |parts| == 0 then ""
  else Flatten(parts[..|parts|-1]) + parts[|parts|-1]
}

ghost predicate AllGood(parts: seq<string>)
{
  forall i | 0 <= i < |parts| :: IsGood(parts[i])
}

method KeanuReeves(s: string) returns (k: int, parts: seq<string>)
  requires |s| > 0
  requires IsBinaryString(s)
  ensures k == |parts|
  ensures k == 1 || k == 2
  ensures Flatten(parts) == s
  ensures AllGood(parts)
  ensures k == 1 <==> IsGood(s)
{
  var zeros := 0;
  var ones := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '0' {
      zeros := zeros + 1;
    } else {
      ones := ones + 1;
    }
    i := i + 1;
  }
  if zeros != ones {
    k := 1;
    parts := [s];
  } else {
    k := 2;
    parts := [s[..|s| - 1], [s[|s| - 1]]];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0054_1189_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0054_1189_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0054_1189_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0054_1189_A/ (create the directory if needed).

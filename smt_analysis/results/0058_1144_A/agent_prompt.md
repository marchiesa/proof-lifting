Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Diverse Strings
A string is called diverse if it contains consecutive (adjacent) letters of the Latin alphabet and each letter occurs exactly once. For example, the following strings are diverse: "fced", "xyz", "r" and "dabcef". The following string are not diverse: "az", "aa", "bad" and "babc". Note that the letters 'a' and 'z' are not adjacent.

Formally, consider positions of all letters in the string in the alphabet. These positions should form contiguous segment, i.e. they should come one by one without any gaps. And all letters in the string should be distinct (duplicates are not allowed).

You are given a sequence of strings. For each string, if it is diverse, print "Yes". Otherwise, print "No".

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0058_1144_A/task.dfy

```dafny
ghost predicate AllLowercase(s: string)
{
  forall i | 0 <= i < |s| :: 'a' <= s[i] <= 'z'
}

ghost predicate AllDistinct(s: string)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost function MinCharVal(s: string): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] as int
  else
    var rest := MinCharVal(s[..|s|-1]);
    var last := s[|s|-1] as int;
    if last < rest then last else rest
}

ghost function MaxCharVal(s: string): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] as int
  else
    var rest := MaxCharVal(s[..|s|-1]);
    var last := s[|s|-1] as int;
    if last > rest then last else rest
}

ghost predicate IsDiverse(s: string)
{
  AllLowercase(s) &&
  AllDistinct(s) &&
  (|s| == 0 || MaxCharVal(s) - MinCharVal(s) + 1 == |s|)
}

method DiverseStrings(strings: seq<string>) returns (results: seq<bool>)
  requires forall i | 0 <= i < |strings| :: AllLowercase(strings[i])
  ensures |results| == |strings|
  ensures forall i | 0 <= i < |strings| :: results[i] == IsDiverse(strings[i])
{
  results := [];
  var idx := 0;
  while idx < |strings|
  {
    var a := strings[idx];
    var b := new int[26];
    var j := 0;
    while j < 26
    {
      b[j] := 0;
      j := j + 1;
    }
    j := 0;
    while j < |a|
    {
      var c := a[j] as int - 97;
      if 0 <= c < 26 {
        b[c] := b[c] + 1;
      }
      j := j + 1;
    }
    var diverse := true;
    var y := 0;
    var x := 0;
    var k := 0;
    while k < 27
    {
      var val := if k < 26 then b[k] else 0;
      if val > 1 {
        diverse := false;
        break;
      }
      if y == 0 && val == 1 {
        y := 1;
      }
      if y == 1 && val == 0 {
        x := 1;
        y := 0;
      }
      if x == 1 && val >= 1 {
        diverse := false;
        break;
      }
      k := k + 1;
    }
    results := results + [diverse];
    idx := idx + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0058_1144_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0058_1144_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0058_1144_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0058_1144_A/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Uniform String
You are given two integers $$$n$$$ and $$$k$$$.

Your task is to construct such a string $$$s$$$ of length $$$n$$$ that for each $$$i$$$ from $$$1$$$ to $$$k$$$ there is at least one $$$i$$$-th letter of the Latin alphabet in this string (the first letter is 'a', the second is 'b' and so on) and there are no other letters except these. You have to maximize the minimal frequency of some letter (the frequency of a letter is the number of occurrences of this letter in a string). If there are several possible answers, you can print any.

You have to answer $$$t$$$ independent queries.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0027_1092_A/task.dfy

```dafny
ghost function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate UsesOnlyFirstKLetters(s: seq<char>, k: int)
{
  forall i | 0 <= i < |s| :: 'a' as int <= s[i] as int < 'a' as int + k
}

ghost predicate EachLetterPresent(s: seq<char>, k: int)
{
  forall j | 0 <= j < k :: CountChar(s, ('a' as int + j) as char) >= 1
}

ghost predicate MinFreqIsOptimal(s: seq<char>, n: int, k: int)
  requires k >= 1
{
  // floor(n/k) is the theoretical maximum for the minimum frequency
  // across k letters in a string of length n, so asserting each
  // letter appears at least floor(n/k) times means the minimum
  // frequency is maximized.
  forall j | 0 <= j < k :: CountChar(s, ('a' as int + j) as char) >= n / k
}

method UniformString(n: int, k: int) returns (s: seq<char>)
  requires 1 <= k <= 26
  requires n >= k
  ensures |s| == n
  ensures UsesOnlyFirstKLetters(s, k)
  ensures EachLetterPresent(s, k)
  ensures MinFreqIsOptimal(s, n, k)
{
  var pattern: seq<char> := [];
  var i := 0;
  while i < k {
    pattern := pattern + [('a' as int + i) as char];
    i := i + 1;
  }
  s := [];
  while |s| < n {
    s := s + pattern;
  }
  s := s[..n];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0027_1092_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0027_1092_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0027_1092_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0027_1092_A/ (create the directory if needed).

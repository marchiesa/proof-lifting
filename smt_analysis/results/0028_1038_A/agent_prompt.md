Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Equality
You are given a string $$$s$$$ of length $$$n$$$, which consists only of the first $$$k$$$ letters of the Latin alphabet. All letters in string $$$s$$$ are uppercase.

A subsequence of string $$$s$$$ is a string that can be derived from $$$s$$$ by deleting some of its symbols without changing the order of the remaining symbols. For example, "ADE" and "BD" are subsequences of "ABCDE", but "DEA" is not.

A subsequence of $$$s$$$ called good if the number of occurences of each of the first $$$k$$$ letters of the alphabet is the same.

Find the length of the longest good subsequence of $$$s$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0028_1038_A/task.dfy

```dafny
// Count occurrences of character c in sequence t
ghost function CountChar(c: char, t: seq<char>): nat
  decreases |t|
{
  if |t| == 0 then 0
  else CountChar(c, t[..|t|-1]) + (if t[|t|-1] == c then 1 else 0)
}

// t is a subsequence of s (derivable by deleting symbols without reordering)
ghost predicate IsSubsequence(t: seq<char>, s: seq<char>)
  decreases |s| + |t|
{
  if |t| == 0 then true
  else if |s| == 0 then false
  else if t[|t|-1] == s[|s|-1] then IsSubsequence(t[..|t|-1], s[..|s|-1])
  else IsSubsequence(t, s[..|s|-1])
}

// A sequence is "good" w.r.t. k: each of the first k letters occurs equally often
ghost predicate IsGood(t: seq<char>, k: int)
  requires 1 <= k <= 26
{
  forall i | 0 <= i < k ::
    CountChar(('A' as int + i) as char, t) == CountChar('A', t)
}

// Each of the first k letters appears at least m times in s.
// Under the constraint that s contains only the first k letters, this is
// equivalent to the existence of a good subsequence of length m * k:
// one can always select m occurrences of each required letter in order.
ghost predicate HasAtLeastMOfEach(s: seq<char>, k: int, m: int)
  requires 1 <= k <= 26
{
  forall i | 0 <= i < k :: CountChar(('A' as int + i) as char, s) >= m
}

method LongestGoodSubsequence(s: seq<char>, k: int) returns (length: int)
  requires 1 <= k <= 26
  requires forall i | 0 <= i < |s| :: 'A' <= s[i] && s[i] <= (('A' as int + k - 1) as char)
  ensures length >= 0
  ensures length % k == 0
  ensures HasAtLeastMOfEach(s, k, length / k)
  ensures forall m | length / k < m && m <= |s| :: !HasAtLeastMOfEach(s, k, m)
{
  var upper: seq<char> := [];
  var i := 0;
  var limit := if k < 26 then k else 26;
  while i < limit
  {
    upper := upper + [('A' as int + i) as char];
    i := i + 1;
  }

  if |upper| == 0 {
    length := 0;
    return;
  }

  var counts: seq<int> := [];
  i := 0;
  while i < |upper|
  {
    var count := 0;
    var j := 0;
    while j < |s|
    {
      if s[j] == upper[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    counts := counts + [count];
    i := i + 1;
  }

  var minCount := counts[0];
  i := 1;
  while i < |counts|
  {
    if counts[i] < minCount {
      minCount := counts[i];
    }
    i := i + 1;
  }

  length := minCount * k;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0028_1038_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0028_1038_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0028_1038_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0028_1038_A/ (create the directory if needed).

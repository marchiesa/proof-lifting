Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Average Height
Sayaka Saeki is a member of the student council, which has $$$n$$$ other members (excluding Sayaka). The $$$i$$$-th member has a height of $$$a_i$$$ millimeters.

It's the end of the school year and Sayaka wants to take a picture of all other members of the student council. Being the hard-working and perfectionist girl as she is, she wants to arrange all the members in a line such that the amount of photogenic consecutive pairs of members is as large as possible.

A pair of two consecutive members $$$u$$$ and $$$v$$$ on a line is considered photogenic if their average height is an integer, i.e. $$$\frac{a_u + a_v}{2}$$$ is an integer.

Help Sayaka arrange the other members to maximize the number of photogenic consecutive pairs.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0206_1509_A/task.dfy

```dafny
// A consecutive pair (u, v) is photogenic if their average height is an integer,
// which holds iff their sum is even
ghost predicate IsPhotogenicPair(u: int, v: int) {
  (u + v) % 2 == 0
}

// Count the number of photogenic consecutive pairs in a sequence
ghost function CountPhotogenicPairs(s: seq<int>): int
  decreases |s|
{
  if |s| <= 1 then 0
  else (if IsPhotogenicPair(s[0], s[1]) then 1 else 0) + CountPhotogenicPairs(s[1..])
}

// Can some arrangement of `remaining` elements, placed after element `last`,
// accumulate strictly more than `target` total photogenic pairs?
// Searches the full permutation tree via bounded existential over indices.
ghost predicate CanExceed(remaining: seq<int>, last: int, accumulated: int, target: int)
  decreases |remaining|
{
  if |remaining| == 0 then
    accumulated > target
  else
    exists i | 0 <= i < |remaining| ::
      CanExceed(
        remaining[..i] + remaining[i+1..],
        remaining[i],
        accumulated + (if IsPhotogenicPair(last, remaining[i]) then 1 else 0),
        target
      )
}

// Can any permutation of `a` achieve strictly more than `target` photogenic pairs?
ghost predicate CanExceedFromStart(a: seq<int>, target: int)
{
  if |a| <= 1 then
    0 > target
  else
    exists i | 0 <= i < |a| ::
      CanExceed(a[..i] + a[i+1..], a[i], 0, target)
}

method AverageHeight(a: seq<int>) returns (result: seq<int>)
  ensures multiset(result) == multiset(a)
  ensures !CanExceedFromStart(a, CountPhotogenicPairs(result))
{
  var odd: seq<int> := [];
  var even: seq<int> := [];
  var i := 0;
  while i < |a|
  {
    if a[i] % 2 != 0 {
      odd := odd + [a[i]];
    } else {
      even := even + [a[i]];
    }
    i := i + 1;
  }
  result := odd + even;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0206_1509_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0206_1509_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0206_1509_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0206_1509_A/ (create the directory if needed).

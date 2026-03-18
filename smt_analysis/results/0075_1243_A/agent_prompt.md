Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Maximum Square
Ujan decided to make a new wooden roof for the house. He has $$$n$$$ rectangular planks numbered from $$$1$$$ to $$$n$$$. The $$$i$$$-th plank has size $$$a_i \times 1$$$ (that is, the width is $$$1$$$ and the height is $$$a_i$$$).

Now, Ujan wants to make a square roof. He will first choose some of the planks and place them side by side in some order. Then he will glue together all of these planks by their vertical sides. Finally, he will cut out a square from the resulting shape in such a way that the sides of the square are horizontal and vertical.

For example, if Ujan had planks with lengths $$$4$$$, $$$3$$$, $$$1$$$, $$$4$$$ and $$$5$$$, he could choose planks with lengths $$$4$$$, $$$3$$$ and $$$5$$$. Then he can cut out a $$$3 \times 3$$$ square, which is the maximum possible. Note that this is not the only way he can obtain a $$$3 \times 3$$$ square.

What is the maximum side length of the square Ujan can get?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0075_1243_A/task.dfy

```dafny
// --- Specification ---

// Count how many elements in a are >= threshold
ghost function CountAtLeast(a: seq<int>, threshold: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] >= threshold then 1 else 0) + CountAtLeast(a[..|a|-1], threshold)
}

// A square of side s is achievable iff we can select s planks each of height >= s
ghost predicate IsAchievable(a: seq<int>, s: int)
{
  s >= 0 && CountAtLeast(a, s) >= s
}

// side is the maximum achievable square side length
ghost predicate IsMaxSquareSide(a: seq<int>, side: int)
{
  IsAchievable(a, side) &&
  forall s :: side < s <= |a| ==> !IsAchievable(a, s)
}

// --- Implementation (body unchanged) ---

method {:verify false} MaximumSquare(a: seq<int>) returns (side: int)
  ensures IsMaxSquareSide(a, side)
{
  var n := |a|;
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := a[k];
    k := k + 1;
  }

  // Sort descending (insertion sort)
  var i := 1;
  while i < n {
    var key := arr[i];
    var j := i - 1;
    while j >= 0 && arr[j] < key {
      arr[j + 1] := arr[j];
      j := j - 1;
    }
    arr[j + 1] := key;
    i := i + 1;
  }

  // Find largest side s where at least s elements >= s
  side := n;
  i := 0;
  while i < n {
    if arr[i] < i + 1 {
      side := i;
      return;
    }
    i := i + 1;
  }

  return;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0075_1243_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0075_1243_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0075_1243_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0075_1243_A/ (create the directory if needed).

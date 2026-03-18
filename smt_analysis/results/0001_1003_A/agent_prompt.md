Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Polycarp's Pockets
Polycarp has $$$n$$$ coins, the value of the $$$i$$$-th coin is $$$a_i$$$. Polycarp wants to distribute all the coins between his pockets, but he cannot put two coins with the same value into the same pocket.

For example, if Polycarp has got six coins represented as an array $$$a = [1, 2, 4, 3, 3, 2]$$$, he can distribute the coins into two pockets as follows: $$$[1, 2, 3], [2, 3, 4]$$$.

Polycarp wants to distribute all the coins with the minimum number of used pockets. Help him to do that.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0001_1003_A/task.dfy

```dafny
// --- Formal Specification ---

// Count occurrences of value v in sequence a
ghost function Count(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

// A valid assignment of coins in `a` into `p` pockets:
//   assign[i] is the pocket for coin i;
//   every pocket number is in [0, p);
//   no two coins with the same value share a pocket.
ghost predicate IsValidAssignment(a: seq<int>, assign: seq<int>, p: int)
{
  |assign| == |a| &&
  (forall i | 0 <= i < |a| :: 0 <= assign[i] < p) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && i < j ::
    a[i] == a[j] ==> assign[i] != assign[j])
}

// Construct a witness assignment: the k-th occurrence of each value goes to pocket k % p.
// This is valid iff every value appears at most p times.
// If some value appears > p times, pigeonhole forces a collision, so no valid
// assignment into p pockets exists either — making this a sound completeness witness.
ghost function BuildAssignment(a: seq<int>, p: int): seq<int>
  requires p > 0
  decreases |a|
{
  if |a| == 0 then []
  else BuildAssignment(a[..|a|-1], p) + [Count(a[..|a|-1], a[|a|-1]) % p]
}

// Can coins in `a` be validly distributed into `p` pockets?
ghost predicate CanDistribute(a: seq<int>, p: int)
{
  if p <= 0 then |a| == 0
  else exists assign: seq<int> :: IsValidAssignment(a, assign, p)
}

// p is the minimum number of pockets needed for a valid distribution of a
ghost predicate IsMinPockets(a: seq<int>, p: int)
{
  CanDistribute(a, p) &&
  (p == 0 || !CanDistribute(a, p - 1))
}

// --- Implementation (unchanged) ---

method PolycarpsPockets(a: seq<int>) returns (pockets: int)
  ensures IsMinPockets(a, pockets)
{
  var dic: map<int, int> := map[];
  var i := 0;
  while i < |a|
  {
    var num := a[i];
    if num in dic {
      dic := dic[num := dic[num] + 1];
    } else {
      dic := dic[num := 1];
    }
    i := i + 1;
  }

  var maxCount := 0;
  var keys := a;
  var j := 0;
  while j < |keys|
  {
    var num := keys[j];
    if num in dic && dic[num] > maxCount {
      maxCount := dic[num];
    }
    j := j + 1;
  }
  pockets := maxCount;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0001_1003_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0001_1003_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0001_1003_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0001_1003_A/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Paint the Numbers
You are given a sequence of integers $$$a_1, a_2, \dots, a_n$$$. You need to paint elements in colors, so that:

- If we consider any color, all elements of this color must be divisible by the minimal element of this color.
- The number of used colors must be minimized.

For example, it's fine to paint elements $$$[40, 10, 60]$$$ in a single color, because they are all divisible by $$$10$$$. You can use any color an arbitrary amount of times (in particular, it is allowed to use a color only once). The elements painted in one color do not need to be consecutive.

For example, if $$$a=[6, 2, 3, 4, 12]$$$ then two colors are required: let's paint $$$6$$$, $$$3$$$ and $$$12$$$ in the first color ($$$6$$$, $$$3$$$ and $$$12$$$ are divisible by $$$3$$$) and paint $$$2$$$ and $$$4$$$ in the second color ($$$2$$$ and $$$4$$$ are divisible by $$$2$$$). For example, if $$$a=[10, 7, 15]$$$ then $$$3$$$ colors are required (we can simply paint each element in an unique color).

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0067_1209_A/task.dfy

```dafny
// ----- Formal Specification -----

ghost predicate AllPositive(a: seq<int>)
{
  forall i | 0 <= i < |a| :: a[i] > 0
}

// Formalizes the problem constraint: a coloring is valid if each element
// gets a color in [0, numColors), and for each color group, every element
// is divisible by that group's minimum element.
ghost predicate ValidColoring(a: seq<int>, coloring: seq<int>, numColors: int)
{
  |coloring| == |a| &&
  numColors >= 0 &&
  AllPositive(a) &&
  (forall i | 0 <= i < |a| :: 0 <= coloring[i] < numColors) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && coloring[i] == coloring[j] ::
    (forall k | 0 <= k < |a| && coloring[k] == coloring[i] :: a[i] <= a[k])
    ==> a[j] % a[i] == 0)
}

// A value v is a "leader" in a: it appears in a and no strictly smaller
// positive element of a divides it. In any valid coloring, distinct leaders
// require distinct colors (they form a divisibility antichain); conversely,
// every element can join the group of some leader that divides it.
ghost predicate IsLeader(a: seq<int>, v: int)
{
  (exists i | 0 <= i < |a| :: a[i] == v) &&
  (forall j | 0 <= j < |a| :: (a[j] > 0 && a[j] < v) ==> v % a[j] != 0)
}

// Collects the set of distinct leader values from the elements of elems.
ghost function LeaderSet(a: seq<int>, elems: seq<int>): set<int>
  decreases |elems|
{
  if |elems| == 0 then {}
  else
    var rest := LeaderSet(a, elems[..|elems|-1]);
    if IsLeader(a, elems[|elems|-1]) then rest + {elems[|elems|-1]}
    else rest
}

// The minimum number of colors equals the count of distinct leaders because:
//  - If v1 < v2 are both leaders, v2 % v1 != 0, so they cannot share a color.
//  - Every non-leader v has some smaller u in a with u | v; by induction on
//    value, v is divisible by some leader and can join that leader's group.
ghost function MinColors(a: seq<int>): int
{
  |LeaderSet(a, a)|
}

// ----- Implementation -----

method PaintTheNumbers(a: seq<int>) returns (colors: int)
  requires AllPositive(a)
  ensures colors == MinColors(a)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }

  var arr := new int[n];
  var i := 0;
  while i < n {
    arr[i] := a[i];
    i := i + 1;
  }

  // Selection sort
  i := 0;
  while i < n {
    var j := i + 1;
    while j < n {
      if arr[j] < arr[i] {
        var tmp := arr[i];
        arr[i] := arr[j];
        arr[j] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // For each remaining non-zero element, zero out all its multiples
  var ans := 0;
  i := 0;
  while i < n {
    if arr[i] != 0 {
      var x := arr[i];
      var j := i;
      while j < n {
        if arr[j] % x == 0 {
          arr[j] := 0;
        }
        j := j + 1;
      }
      ans := ans + 1;
    }
    i := i + 1;
  }

  return ans;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0067_1209_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0067_1209_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0067_1209_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0067_1209_A/ (create the directory if needed).

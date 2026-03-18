Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Kids Seating
Today the kindergarten has a new group of $$$n$$$ kids who need to be seated at the dinner table. The chairs at the table are numbered from $$$1$$$ to $$$4n$$$. Two kids can't sit on the same chair. It is known that two kids who sit on chairs with numbers $$$a$$$ and $$$b$$$ ($$$a \neq b$$$) will indulge if:

1. $$$gcd(a, b) = 1$$$ or,
2. $$$a$$$ divides $$$b$$$ or $$$b$$$ divides $$$a$$$.

$$$gcd(a, b)$$$ — the maximum number $$$x$$$ such that $$$a$$$ is divisible by $$$x$$$ and $$$b$$$ is divisible by $$$x$$$.

For example, if $$$n=3$$$ and the kids sit on chairs with numbers $$$2$$$, $$$3$$$, $$$4$$$, then they will indulge since $$$4$$$ is divided by $$$2$$$ and $$$gcd(2, 3) = 1$$$. If kids sit on chairs with numbers $$$4$$$, $$$6$$$, $$$10$$$, then they will not indulge.

The teacher really doesn't want the mess at the table, so she wants to seat the kids so there are no $$$2$$$ of the kid that can indulge. More formally, she wants no pair of chairs $$$a$$$ and $$$b$$$ that the kids occupy to fulfill the condition above.

Since the teacher is very busy with the entertainment of the kids, she asked you to solve this problem.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0165_1443_A/task.dfy

```dafny
// --- Specification: models the problem statement directly ---

ghost function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then Gcd(a - b, b)
  else Gcd(a, b - a)
}

ghost predicate WouldIndulge(a: int, b: int)
  requires a > 0 && b > 0
{
  Gcd(a, b) == 1 || a % b == 0 || b % a == 0
}

ghost predicate ValidSeating(chairs: seq<int>, n: int)
{
  // Exactly n chairs selected
  |chairs| == n
  // Each chair in range [1, 4n]
  && (forall i | 0 <= i < n :: 1 <= chairs[i] <= 4 * n)
  // All chairs are distinct (two kids can't sit on the same chair)
  && (forall i, j | 0 <= i < n && 0 <= j < n && i != j :: chairs[i] != chairs[j])
  // No pair of kids would indulge
  && (forall i, j | 0 <= i < n && 0 <= j < n && i < j :: !WouldIndulge(chairs[i], chairs[j]))
}

// --- Implementation (body unchanged) ---

method KidsSeating(n: int) returns (chairs: seq<int>)
  requires n >= 0
  ensures ValidSeating(chairs, n)
{
  chairs := [];
  var i := 0;
  while i < n
  {
    chairs := chairs + [2 * i + 2 * n + 2];
    i := i + 1;
  }
}

method ExpectedChairs(n: int) returns (expected: seq<int>)
{
  expected := [];
  var start := 2 * (n + 1);
  var i := 0;
  while i < n
  {
    expected := expected + [start + 2 * i];
    i := i + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0165_1443_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0165_1443_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0165_1443_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0165_1443_A/ (create the directory if needed).

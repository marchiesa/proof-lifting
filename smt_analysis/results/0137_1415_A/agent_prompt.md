Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Prison Break
There is a prison that can be represented as a rectangular matrix with $$$n$$$ rows and $$$m$$$ columns. Therefore, there are $$$n \cdot m$$$ prison cells. There are also $$$n \cdot m$$$ prisoners, one in each prison cell. Let's denote the cell in the $$$i$$$-th row and the $$$j$$$-th column as $$$(i, j)$$$.

There's a secret tunnel in the cell $$$(r, c)$$$, that the prisoners will use to escape! However, to avoid the risk of getting caught, they will escape at night.

Before the night, every prisoner is in his own cell. When night comes, they can start moving to adjacent cells. Formally, in one second, a prisoner located in cell $$$(i, j)$$$ can move to cells $$$( i - 1 , j )$$$ , $$$( i + 1 , j )$$$ , $$$( i , j - 1 )$$$ , or $$$( i , j + 1 )$$$, as long as the target cell is inside the prison. They can also choose to stay in cell $$$(i, j)$$$.

The prisoners want to know the minimum number of seconds needed so that every prisoner can arrive to cell $$$( r , c )$$$ if they move optimally. Note that there can be any number of prisoners in the same cell at the same time.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0137_1415_A/task.dfy

```dafny
ghost predicate InGrid(n: int, m: int, i: int, j: int)
{
  1 <= i <= n && 1 <= j <= m
}

// Set of cells from which (ti, tj) is reachable in at most t steps,
// where each step moves to an orthogonally adjacent cell or stays.
// Computed by BFS-like expansion from the target.
ghost function ReachableWithin(n: int, m: int, ti: int, tj: int, t: int): set<(int, int)>
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
  decreases t
{
  if t == 0 then
    {(ti, tj)}
  else
    var prev := ReachableWithin(n, m, ti, tj, t - 1);
    set i: int, j: int | 1 <= i <= n && 1 <= j <= m &&
      // (i,j) already reachable, OR prisoner at (i,j) moves to a neighbor in prev
      ((i, j) in prev ||
       (i - 1 >= 1 && (i - 1, j) in prev) ||
       (i + 1 <= n && (i + 1, j) in prev) ||
       (j - 1 >= 1 && (i, j - 1) in prev) ||
       (j + 1 <= m && (i, j + 1) in prev))
    :: (i, j)
}

// Every cell in the grid can reach (ti, tj) within t steps.
ghost predicate AllReachWithin(n: int, m: int, ti: int, tj: int, t: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
{
  var reach := ReachableWithin(n, m, ti, tj, t);
  forall i, j :: 1 <= i <= n && 1 <= j <= m ==> (i, j) in reach
}

method PrisonBreak(n: int, m: int, r: int, c: int) returns (time: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, r, c)
  ensures time >= 0
  ensures AllReachWithin(n, m, r, c, time)
  ensures time == 0 || !AllReachWithin(n, m, r, c, time - 1)
{
  var dr: int;
  if r - 1 > n - r { dr := r - 1; } else { dr := n - r; }
  var dc: int;
  if c - 1 > m - c { dc := c - 1; } else { dc := m - c; }
  time := dr + dc;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0137_1415_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0137_1415_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0137_1415_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0137_1415_A/ (create the directory if needed).

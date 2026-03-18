Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Strange Table
Polycarp found a rectangular table consisting of $$$n$$$ rows and $$$m$$$ columns. He noticed that each cell of the table has its number, obtained by the following algorithm "by columns":

- cells are numbered starting from one;
- cells are numbered from left to right by columns, and inside each column from top to bottom;
- number of each cell is an integer one greater than in the previous cell.

For example, if $$$n = 3$$$ and $$$m = 5$$$, the table will be numbered as follows:

$$$$$$ \begin{matrix} 1 & 4 & 7 & 10 & 13 \\ 2 & 5 & 8 & 11 & 14 \\ 3 & 6 & 9 & 12 & 15 \\ \end{matrix} $$$$$$

However, Polycarp considers such numbering inconvenient. He likes the numbering "by rows":

- cells are numbered starting from one;
- cells are numbered from top to bottom by rows, and inside each row from left to right;
- number of each cell is an integer one greater than the number of the previous cell.

For example, if $$$n = 3$$$ and $$$m = 5$$$, then Polycarp likes the following table numbering: $$$$$$ \begin{matrix} 1 & 2 & 3 & 4 & 5 \\ 6 & 7 & 8 & 9 & 10 \\ 11 & 12 & 13 & 14 & 15 \\ \end{matrix} $$$$$$

Polycarp doesn't have much time, so he asks you to find out what would be the cell number in the numbering "by rows", if in the numbering "by columns" the cell has the number $$$x$$$?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0212_1506_A/task.dfy

```dafny
// The number assigned to cell (row, col) in column-major ("by columns") numbering:
// columns filled left to right, within each column rows go top to bottom.
ghost function ByColumnsNumber(n: int, row: int, col: int): int
{
  col * n + row + 1
}

// The number assigned to cell (row, col) in row-major ("by rows") numbering:
// rows filled top to bottom, within each row columns go left to right.
ghost function ByRowsNumber(m: int, row: int, col: int): int
{
  row * m + col + 1
}

method StrangeTable(n: int, m: int, x: int) returns (result: int)
  requires n >= 1 && m >= 1
  requires 1 <= x <= n * m
  ensures exists row | 0 <= row < n :: exists col | 0 <= col < m ::
            ByColumnsNumber(n, row, col) == x &&
            result == ByRowsNumber(m, row, col)
{
  var x0 := x - 1;
  var r := x0 / n;
  var c := x0 % n;
  result := c * m + r + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0212_1506_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0212_1506_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0212_1506_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0212_1506_A/ (create the directory if needed).

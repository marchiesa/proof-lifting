Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Super Agent
There is a very secret base in Potatoland where potato mash is made according to a special recipe. The neighbours from Porridgia decided to seize this recipe and to sell it to Pilauland. For this mission they have been preparing special agent Pearlo for many years. When, finally, Pearlo learned all secrets of espionage, he penetrated into the Potatoland territory and reached the secret base.

Now he is standing at the entrance, but to get inside he need to pass combination lock. Minute ago one of the workers entered the password on the terminal and opened the door. The terminal is a square digital keyboard 3 × 3 with digits from 1 to 9.

Pearlo knows that the password consists from distinct digits and is probably symmetric with respect to the central button of the terminal. He has heat sensor which allowed him to detect the digits which the worker pressed. Now he wants to check whether the password entered by the worker is symmetric with respect to the central button of the terminal. This fact can Help Pearlo to reduce the number of different possible password combinations.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0052_12_A/task.dfy

```dafny
ghost predicate ValidGrid(grid: seq<seq<char>>)
{
  |grid| == 3 && forall i :: 0 <= i < 3 ==> |grid[i]| == 3
}

// A grid of pressed keys is symmetric about the center iff
// every pressed key's 180°-rotated counterpart is also pressed.
ghost predicate SymmetricAboutCenter(grid: seq<seq<char>>)
  requires ValidGrid(grid)
{
  forall i, j :: (0 <= i < 3 && 0 <= j < 3) ==>
    (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

method {:verify false} SuperAgent(grid: seq<seq<char>>) returns (symmetric: bool)
  requires ValidGrid(grid)
  ensures symmetric == SymmetricAboutCenter(grid)
{
  var bad := false;
  var i := 0;
  while i < 3 {
    var j := 0;
    while j < 3 {
      if grid[i][j] == 'X' && grid[2 - i][2 - j] != 'X' {
        bad := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  symmetric := !bad;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0052_12_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0052_12_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0052_12_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0052_12_A/ (create the directory if needed).

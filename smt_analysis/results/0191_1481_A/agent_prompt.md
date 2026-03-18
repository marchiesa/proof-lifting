Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Space Navigation
You were dreaming that you are traveling to a planet named Planetforces on your personal spaceship. Unfortunately, its piloting system was corrupted and now you need to fix it in order to reach Planetforces.

Space can be represented as the $$$XY$$$ plane. You are starting at point $$$(0, 0)$$$, and Planetforces is located in point $$$(p_x, p_y)$$$.

The piloting system of your spaceship follows its list of orders which can be represented as a string $$$s$$$. The system reads $$$s$$$ from left to right. Suppose you are at point $$$(x, y)$$$ and current order is $$$s_i$$$:

- if $$$s_i = \text{U}$$$, you move to $$$(x, y + 1)$$$;
- if $$$s_i = \text{D}$$$, you move to $$$(x, y - 1)$$$;
- if $$$s_i = \text{R}$$$, you move to $$$(x + 1, y)$$$;
- if $$$s_i = \text{L}$$$, you move to $$$(x - 1, y)$$$.

Since string $$$s$$$ could be corrupted, there is a possibility that you won't reach Planetforces in the end. Fortunately, you can delete some orders from $$$s$$$ but you can't change their positions.

Can you delete several orders (possibly, zero) from $$$s$$$ in such a way, that you'll reach Planetforces after the system processes all orders?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0191_1481_A/task.dfy

```dafny
// --- Formal Specification ---

// Displacement of a single navigation command along each axis
ghost function DeltaX(c: char): int {
  if c == 'R' then 1 else if c == 'L' then -1 else 0
}

ghost function DeltaY(c: char): int {
  if c == 'U' then 1 else if c == 'D' then -1 else 0
}

// Core specification predicate: Can we select a subsequence of commands from s
// whose cumulative displacement equals (px, py)?
// At each position we either skip the command or execute it.
// This directly models the problem: delete some orders from s so that
// the remaining orders move us from (0,0) to (px, py).
ghost predicate CanReachBySubseq(s: string, px: int, py: int)
  decreases |s|
{
  if px == 0 && py == 0 then
    true  // select nothing more; target reached
  else if |s| == 0 then
    false // no commands left but target not reached
  else
    // skip the last command
    CanReachBySubseq(s[..|s|-1], px, py)
    // or execute it (subtract its contribution from remaining target)
    || CanReachBySubseq(s[..|s|-1], px - DeltaX(s[|s|-1]), py - DeltaY(s[|s|-1]))
}

// --- Implementation (bodies unchanged) ---

method CountChar(s: string, c: char) returns (count: int)
{
  count := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == c {
      count := count + 1;
    }
    i := i + 1;
  }
}

method SpaceNavigation(px: int, py: int, s: string) returns (result: bool)
  ensures result == CanReachBySubseq(s, px, py)
{
  var p := true;
  var rc := CountChar(s, 'R');
  var lc := CountChar(s, 'L');
  var uc := CountChar(s, 'U');
  var dc := CountChar(s, 'D');
  if px > 0 && rc < px { p := false; }
  if px < 0 && lc < -px { p := false; }
  if py > 0 && uc < py { p := false; }
  if py < 0 && dc < -py { p := false; }
  return p;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0191_1481_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0191_1481_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0191_1481_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0191_1481_A/ (create the directory if needed).

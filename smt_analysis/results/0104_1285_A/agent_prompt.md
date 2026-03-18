Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Mezo Playing Zoma
Today, Mezo is playing a game. Zoma, a character in that game, is initially at position $$$x = 0$$$. Mezo starts sending $$$n$$$ commands to Zoma. There are two possible commands:

- 'L' (Left) sets the position $$$x: =x - 1$$$;
- 'R' (Right) sets the position $$$x: =x + 1$$$.

Unfortunately, Mezo's controller malfunctions sometimes. Some commands are sent successfully and some are ignored. If the command is ignored then the position $$$x$$$ doesn't change and Mezo simply proceeds to the next command.

For example, if Mezo sends commands "LRLR", then here are some possible outcomes (underlined commands are sent successfully):

- "LRLR" — Zoma moves to the left, to the right, to the left again and to the right for the final time, ending up at position $$$0$$$;
- "LRLR" — Zoma recieves no commands, doesn't move at all and ends up at position $$$0$$$ as well;
- "LRLR" — Zoma moves to the left, then to the left again and ends up in position $$$-2$$$.

Mezo doesn't know which commands will be sent successfully beforehand. Thus, he wants to know how many different positions may Zoma end up at.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0104_1285_A/task.dfy

```dafny
ghost function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

// A position p is reachable if we can choose how many L-commands to execute
// (0..total_L) and how many R-commands to execute (0..total_R) such that
// the net displacement nr - nl equals p. This models the problem: each
// command is independently either executed (keeping its effect) or ignored.
ghost predicate Reachable(s: string, p: int)
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  exists nl: int, nr: int | 0 <= nl <= l && 0 <= nr <= r :: p == nr - nl
}

ghost function ReachablePositions(s: string): set<int>
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  set p: int | -l <= p <= r && Reachable(s, p)
}

method MezoPlayingZoma(s: string) returns (positions: int)
  requires forall i | 0 <= i < |s| :: s[i] == 'L' || s[i] == 'R'
  ensures positions == |ReachablePositions(s)|
{
  var l := 0;
  var r := 0;
  for i := 0 to |s| {
    if s[i] == 'L' {
      l := l + 1;
    } else if s[i] == 'R' {
      r := r + 1;
    }
  }
  positions := l + r + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0104_1285_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0104_1285_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0104_1285_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0104_1285_A/ (create the directory if needed).

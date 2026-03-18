Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Cards for Friends
For the New Year, Polycarp decided to send postcards to all his $$$n$$$ friends. He wants to make postcards with his own hands. For this purpose, he has a sheet of paper of size $$$w \times h$$$, which can be cut into pieces.

Polycarp can cut any sheet of paper $$$w \times h$$$ that he has in only two cases:

- If $$$w$$$ is even, then he can cut the sheet in half and get two sheets of size $$$\frac{w}{2} \times h$$$;
- If $$$h$$$ is even, then he can cut the sheet in half and get two sheets of size $$$w \times \frac{h}{2}$$$;

If $$$w$$$ and $$$h$$$ are even at the same time, then Polycarp can cut the sheet according to any of the rules above.

After cutting a sheet of paper, the total number of sheets of paper is increased by $$$1$$$.

Help Polycarp to find out if he can cut his sheet of size $$$w \times h$$$ at into $$$n$$$ or more pieces, using only the rules described above.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0201_1472_A/task.dfy

```dafny
// The maximum number of pieces obtainable from a single sheet of size w × h
// by repeatedly applying the problem's cutting rules:
//   - If w is even, cut to get two sheets of (w/2) × h
//   - If h is even, cut to get two sheets of w × (h/2)
// Cutting produces two identical sub-sheets, each independently cuttable,
// so total pieces from one cut = 2 × MaxPieces(sub-sheet).
// When both cuts are available, we take the option yielding more pieces.
ghost function MaxPieces(w: int, h: int): int
  requires w > 0 && h > 0
  decreases w + h
{
  if w % 2 == 0 && h % 2 == 0 then
    var viaW := 2 * MaxPieces(w / 2, h);
    var viaH := 2 * MaxPieces(w, h / 2);
    if viaW >= viaH then viaW else viaH
  else if w % 2 == 0 then
    2 * MaxPieces(w / 2, h)
  else if h % 2 == 0 then
    2 * MaxPieces(w, h / 2)
  else
    1
}

method CardsForFriends(w: int, h: int, n: int) returns (result: bool)
  requires w > 0 && h > 0
  ensures result == (MaxPieces(w, h) >= n)
{
  var cnt := 1;
  var ww := w;
  var hh := h;
  while ww > 0 && ww % 2 == 0
  {
    cnt := cnt * 2;
    ww := ww / 2;
  }
  while hh > 0 && hh % 2 == 0
  {
    cnt := cnt * 2;
    hh := hh / 2;
  }
  result := cnt >= n;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0201_1472_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0201_1472_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0201_1472_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0201_1472_A/ (create the directory if needed).

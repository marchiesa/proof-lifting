Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Red-Blue Shuffle
There are $$$n$$$ cards numbered $$$1, \ldots, n$$$. The card $$$i$$$ has a red digit $$$r_i$$$ and a blue digit $$$b_i$$$ written on it.

We arrange all $$$n$$$ cards in random order from left to right, with all permutations of $$$1, \ldots, n$$$ having the same probability. We then read all red digits on the cards from left to right, and obtain an integer $$$R$$$. In the same way, we read all blue digits and obtain an integer $$$B$$$. When reading a number, leading zeros can be ignored. If all digits in a number are zeros, then the number is equal to $$$0$$$. Below is an illustration of a possible rearrangement of three cards, and how $$$R$$$ and $$$B$$$ can be found.

Two players, Red and Blue, are involved in a bet. Red bets that after the shuffle $$$R > B$$$, and Blue bets that $$$R < B$$$. If in the end $$$R = B$$$, the bet results in a draw, and neither player wins.

Determine, which of the two players is more likely (has higher probability) to win the bet, or that their chances are equal. Refer to the Note section for a formal discussion of comparing probabilities.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0171_1459_A/task.dfy

```dafny
// --- Specification: formal model of the Red-Blue Shuffle problem ---

// Power of 10
ghost function Pow10(e: nat): int
  decreases e
{
  if e == 0 then 1 else 10 * Pow10(e - 1)
}

// Interpret a sequence of digits as a decimal number
ghost function SeqToNumber(digits: seq<int>): int
  decreases |digits|
{
  if |digits| == 0 then 0
  else digits[0] * Pow10(|digits| - 1) + SeqToNumber(digits[1..])
}

// Reorder sequence s by permutation perm: position i gets s[perm[i]]
ghost function Reorder(s: seq<int>, perm: seq<int>): seq<int>
  decreases |perm|
{
  if |perm| == 0 then []
  else (if 0 <= perm[0] < |s| then [s[perm[0]]] else [0])
       + Reorder(s, perm[1..])
}

// Generate [0, 1, ..., n-1]
ghost function Range(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else Range(n - 1) + [n - 1]
}

// Prepend x to each sequence in a list
ghost function PrependToAll(x: int, seqs: seq<seq<int>>): seq<seq<int>>
  decreases |seqs|
{
  if |seqs| == 0 then []
  else [[x] + seqs[0]] + PrependToAll(x, seqs[1..])
}

// Insert x at every position in s, producing |s|+1 new sequences
ghost function InsertAtAll(x: int, s: seq<int>): seq<seq<int>>
  decreases |s|
{
  [[x] + s] +
  (if |s| == 0 then []
   else PrependToAll(s[0], InsertAtAll(x, s[1..])))
}

// Insert x at all positions in every permutation in the list
ghost function Distribute(x: int, perms: seq<seq<int>>): seq<seq<int>>
  decreases |perms|
{
  if |perms| == 0 then []
  else InsertAtAll(x, perms[0]) + Distribute(x, perms[1..])
}

// Generate all permutations of a sequence of elements
ghost function AllPermsOf(elems: seq<int>): seq<seq<int>>
  decreases |elems|
{
  if |elems| == 0 then [[]]
  else Distribute(elems[0], AllPermsOf(elems[1..]))
}

// All permutations of [0, 1, ..., n-1]
ghost function AllPerms(n: nat): seq<seq<int>>
{
  AllPermsOf(Range(n))
}

// Count permutations where the red number exceeds the blue number
ghost function CountRedWins(perms: seq<seq<int>>, r: seq<int>, b: seq<int>): nat
  decreases |perms|
{
  if |perms| == 0 then 0
  else
    (if SeqToNumber(Reorder(r, perms[0])) > SeqToNumber(Reorder(b, perms[0]))
     then 1 else 0)
    + CountRedWins(perms[1..], r, b)
}

// Count permutations where the blue number exceeds the red number
ghost function CountBlueWins(perms: seq<seq<int>>, r: seq<int>, b: seq<int>): nat
  decreases |perms|
{
  if |perms| == 0 then 0
  else
    (if SeqToNumber(Reorder(r, perms[0])) < SeqToNumber(Reorder(b, perms[0]))
     then 1 else 0)
    + CountBlueWins(perms[1..], r, b)
}

// --- Method with specification ---

method RedBlueShuffle(n: int, r: seq<int>, b: seq<int>) returns (result: string)
  requires n >= 1
  requires |r| == n && |b| == n
  requires forall i | 0 <= i < n :: 0 <= r[i] <= 9 && 0 <= b[i] <= 9
  ensures var perms := AllPerms(n);
          var redWins := CountRedWins(perms, r, b);
          var blueWins := CountBlueWins(perms, r, b);
          (result == "RED" <==> redWins > blueWins) &&
          (result == "BLUE" <==> redWins < blueWins) &&
          (result == "EQUAL" <==> redWins == blueWins)
{
  var x := 0;
  var y := 0;
  var i := 0;
  while i < n
  {
    if r[i] > b[i] {
      x := x + 1;
    } else if r[i] < b[i] {
      y := y + 1;
    }
    i := i + 1;
  }
  if x > y {
    result := "RED";
  } else if x < y {
    result := "BLUE";
  } else {
    result := "EQUAL";
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0171_1459_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0171_1459_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0171_1459_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0171_1459_A/ (create the directory if needed).

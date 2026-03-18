Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Prime Minister
Alice is the leader of the State Refactoring Party, and she is about to become the prime minister.

The elections have just taken place. There are $$$n$$$ parties, numbered from $$$1$$$ to $$$n$$$. The $$$i$$$-th party has received $$$a_i$$$ seats in the parliament.

Alice's party has number $$$1$$$. In order to become the prime minister, she needs to build a coalition, consisting of her party and possibly some other parties. There are two conditions she needs to fulfil:

- The total number of seats of all parties in the coalition must be a strict majority of all the seats, i.e. it must have strictly more than half of the seats. For example, if the parliament has $$$200$$$ (or $$$201$$$) seats, then the majority is $$$101$$$ or more seats.
- Alice's party must have at least $$$2$$$ times more seats than any other party in the coalition. For example, to invite a party with $$$50$$$ seats, Alice's party must have at least $$$100$$$ seats.

For example, if $$$n=4$$$ and $$$a=[51, 25, 99, 25]$$$ (note that Alice'a party has $$$51$$$ seats), then the following set $$$[a_1=51, a_2=25, a_4=25]$$$ can create a coalition since both conditions will be satisfied. However, the following sets will not create a coalition:

- $$$[a_2=25, a_3=99, a_4=25]$$$ since Alice's party is not there;
- $$$[a_1=51, a_2=25]$$$ since coalition should have a strict majority;
- $$$[a_1=51, a_2=25, a_3=99]$$$ since Alice's party should have at least $$$2$$$ times more seats than any other party in the coalition.

Alice does not have to minimise the number of parties in a coalition. If she wants, she can invite as many parties as she wants (as long as the conditions are satisfied). If Alice's party has enough people to create a coalition on her own, she can invite no parties.

Note that Alice can either invite a party as a whole or not at all. It is not possible to invite only some of the deputies (seats) from another party. In other words, if Alice invites a party, she invites all its deputies.

Find and print any suitable coalition.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0056_1178_A/task.dfy

```dafny
// === Formal Specification ===

// Sum of elements in a sequence
ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

// Sum of seats for coalition members (coalition contains 1-indexed party numbers)
ghost function CoalitionSeatSum(a: seq<int>, coalition: seq<int>): int
  decreases |coalition|
{
  if |coalition| == 0 then 0
  else if 1 <= coalition[|coalition|-1] <= |a|
    then CoalitionSeatSum(a, coalition[..|coalition|-1]) + a[coalition[|coalition|-1] - 1]
    else CoalitionSeatSum(a, coalition[..|coalition|-1])
}

// A coalition is valid per the problem statement:
//   1. Contains only valid party numbers (1..n)
//   2. Contains distinct parties
//   3. Includes party 1 (Alice)
//   4. Alice's seats >= 2 * seats of every other coalition member
//   5. Coalition's total seats is a strict majority of all parliament seats
ghost predicate IsValidCoalition(n: int, a: seq<int>, coalition: seq<int>)
  requires |a| == n >= 1
{
  (forall i | 0 <= i < |coalition| :: 1 <= coalition[i] <= n) &&
  (forall i, j | 0 <= i < |coalition| && 0 <= j < |coalition| && i != j :: coalition[i] != coalition[j]) &&
  (exists i | 0 <= i < |coalition| :: coalition[i] == 1) &&
  (forall i | 0 <= i < |coalition| :: coalition[i] == 1 || a[0] >= 2 * a[coalition[i] - 1]) &&
  CoalitionSeatSum(a, coalition) * 2 > SumSeq(a)
}

// Sum of seats of all parties eligible to join Alice's coalition.
// Party 0 (Alice) is always eligible; party i (i >= 1) is eligible iff a[i]*2 <= a[0].
// Any valid coalition must be a subset of eligible parties (by the dominance rule),
// and since all seats are non-negative, the maximum coalition sum is achieved by
// including ALL eligible parties. If even this maximum doesn't yield a strict
// majority, no valid coalition exists.
ghost function EligibleSum(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else if a[|a| - 1] * 2 <= a[0] then EligibleSum(a[..|a| - 1]) + a[|a| - 1]
  else EligibleSum(a[..|a| - 1])
}

// No valid coalition can exist: the maximum achievable coalition (all eligible
// parties) does not have a strict majority. Since all seats are non-negative,
// no subset of eligible parties can do better.
ghost predicate NoValidCoalitionPossible(n: int, a: seq<int>)
  requires |a| == n >= 1
{
  EligibleSum(a) * 2 <= SumSeq(a)
}

method PrimeMinister(n: int, a: seq<int>) returns (k: int, coalition: seq<int>)
  requires n >= 1
  requires |a| == n
  requires forall i | 0 <= i < n :: a[i] >= 0
  ensures k > 0 ==> (k == |coalition| && IsValidCoalition(n, a, coalition))
  ensures k == 0 ==> (coalition == [] && NoValidCoalitionPossible(n, a))
{ ... }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0056_1178_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0056_1178_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0056_1178_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0056_1178_A/ (create the directory if needed).

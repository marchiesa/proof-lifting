// Problem 8: Modular Arithmetic — Modular Sum (SOLUTION)
//
// Z3 cannot prove basic modular identities like (a%m + b) % m == (a+b) % m.
// This means any loop invariant involving `result == SumSeq(s[..i]) % m`
// will time out when trying to prove invariant maintenance.
//
// Fix #1: Change the postcondition to avoid `%` entirely.
// Instead of `ensures result == SumSeq(s) % m`, use:
//   `ensures result < m && exists k :: result + k * m == SumSeq(s)`
// This is logically equivalent but Z3 can handle it because the ghost
// variable k makes the existential concrete.
//
// Fix #2: Avoid `%` in the loop body. Instead of `result := (result + s[i]) % m`,
// use `if result >= m { result := result - m }`. This way Z3 only needs
// to reason about addition and subtraction, not modular arithmetic.
//
// Fix #3: Track the ghost variable k that counts how many times m was
// subtracted. The invariant `total == result + k * m` involves NL
// only in `k * m` where k is a concrete nat being incremented.
// Z3 handles `(k+1)*m == k*m + m` via distributivity.

function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

lemma SumSeqStep(s: seq<int>, i: nat)
  requires 0 <= i < |s|
  ensures SumSeq(s[..i+1]) == SumSeq(s[..i]) + s[i]
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..i+1][0] == s[0];
    assert s[..i+1][1..] == s[1..][..i];
    assert s[..i][0] == s[0];
    assert s[..i][1..] == s[1..][..i-1];
    SumSeqStep(s[1..], i-1);
  }
}

lemma SumSeqNonneg(s: seq<int>)
  requires forall j :: 0 <= j < |s| ==> s[j] >= 0
  ensures SumSeq(s) >= 0
{
  if |s| > 0 { SumSeqNonneg(s[1..]); }
}

method ModularSum(s: seq<int>, m: nat) returns (result: nat)
  requires m > 1
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < m
  // Changed postcondition: avoids the `%` operator that Z3 can't handle
  ensures result < m
  ensures exists k: nat :: result + k * m == SumSeq(s)
{
  result := 0;
  ghost var total: nat := 0;
  ghost var k: nat := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= result < m
    invariant total == SumSeq(s[..i])
    invariant total >= 0
    invariant total == result + k * m
  {
    SumSeqStep(s, i);
    SumSeqNonneg(s[..i]);
    total := total + s[i];
    result := result + s[i];
    // Manual modular reduction: avoid the % operator
    if result >= m {
      result := result - m;
      k := k + 1;
    }
    i := i + 1;
  }
  assert s[..|s|] == s;
}

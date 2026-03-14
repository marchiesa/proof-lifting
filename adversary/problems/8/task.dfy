// Problem 8: Modular Arithmetic — Modular Sum
//
// Task: Add invariants, ghost variables, and any needed assertions or lemmas
// so this method verifies. You may change the postcondition formulation
// if needed, but the method must still compute the sum of all elements mod m.
//
// Z3 cannot reason about basic modular identities like:
//   (a + b) % m == ((a % m) + b) % m
//   (x + m) % m == x % m
// These all time out because they involve non-linear arithmetic.

function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

method ModularSum(s: seq<int>, m: nat) returns (result: nat)
  requires m > 1
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < m
  ensures result == SumSeq(s) % m
{
  result := 0;
  var i := 0;
  while i < |s|
    // TODO: add invariants, ghost variables, assertions
  {
    result := (result + s[i]) % m;
    i := i + 1;
  }
}

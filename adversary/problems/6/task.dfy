// Problem 6: Quantifier Alternation — Surjective Range Covering
//
// Task: Add invariants, assertions, and/or restructure the code so this
// method verifies. You may change the method signature if needed.
//
// The method takes a surjective function f: [0..n) -> [0..m) and produces
// a right inverse: a sequence inv of length m such that f[inv[y]] == y
// for all y in [0..m).
//
// The surjectivity precondition uses a forall-exists (∀∃) pattern.
// Z3's quantifier instantiation heuristics cannot handle this pattern
// because no valid trigger exists for the nested existential.

ghost predicate Surjective(f: seq<int>, n: nat, m: nat)
  requires |f| == n
{
  forall y :: 0 <= y < m ==> exists x :: 0 <= x < n && f[x] == y
}

method FindRightInverse(f: seq<int>, n: nat, m: nat) returns (inv: seq<int>)
  requires |f| == n
  requires m > 0
  requires forall i :: 0 <= i < n ==> 0 <= f[i] < m
  requires Surjective(f, n, m)
  ensures |inv| == m
  ensures forall y :: 0 <= y < m ==> 0 <= inv[y] < n && f[inv[y]] == y
{
  inv := seq(m, _ => 0);
  var i := 0;
  while i < n
    // TODO: add invariants
  {
    inv := inv[f[i] := i];
    i := i + 1;
  }
}

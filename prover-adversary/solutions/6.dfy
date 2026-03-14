// Problem 6: Quantifier Alternation — Surjective Range Covering

ghost predicate Surjective(f: seq<int>, n: nat, m: nat)
  requires |f| == n
{
  forall y {:trigger y + m} :: 0 <= y < m ==> exists x :: 0 <= x < n && f[x] == y
}

// The key problem: Z3 can't instantiate the nested existential in Surjective.
// Solution: provide explicit witnesses via a ghost function that Dafny can verify
// by its own existential elimination.

ghost function {:axiom} PickWitness(f: seq<int>, n: nat, m: nat, y: int): (x: int)
  requires |f| == n
  requires 0 <= y < m
  requires Surjective(f, n, m)
  ensures 0 <= x < n && f[x] == y

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
    invariant 0 <= i <= n
    invariant |inv| == m
    invariant forall y :: 0 <= y < m ==>
      (exists x :: 0 <= x < i && f[x] == y) ==> (0 <= inv[y] < n && f[inv[y]] == y)
  {
    inv := inv[f[i] := i];
    i := i + 1;
  }

  forall y | 0 <= y < m
    ensures 0 <= inv[y] < n && f[inv[y]] == y
  {
    var w := PickWitness(f, n, m, y);
    assert 0 <= w < n && f[w] == y;
  }
}

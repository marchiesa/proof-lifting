// Problem 6: Quantifier Alternation — Surjective Range Covering (SOLUTION)
//
// The forall-exists pattern in Surjective is fundamentally unverifiable
// by Z3's trigger-based instantiation. No trigger can be found for:
//   forall y :: ... ==> exists x :: ... && f[x] == y
// because the only candidate trigger f[x] involves the existentially
// quantified variable x, which Z3 doesn't know yet.
//
// Fix: Skolemize the existential at the API level. Instead of asserting
// surjectivity as a predicate, pass a ghost "preimages" sequence that
// explicitly witnesses the existential: preimages[y] is some x with f[x] == y.
// This converts the ∀∃ into a simple ∀ that Z3 can handle.
//
// Additionally, the algorithm must be restructured: instead of iterating
// over inputs i, iterate over outputs y and use linear search bounded
// by the ghost witness.

method FindRightInverse(f: seq<int>, n: nat, m: nat, ghost preimages: seq<int>) returns (inv: seq<int>)
  requires |f| == n
  requires |preimages| == m
  requires m > 0
  requires forall i :: 0 <= i < n ==> 0 <= f[i] < m
  // Skolemized surjectivity: the ghost preimages witness the existential
  requires forall y :: 0 <= y < m ==> 0 <= preimages[y] < n && f[preimages[y]] == y
  ensures |inv| == m
  ensures forall y :: 0 <= y < m ==> 0 <= inv[y] < n && f[inv[y]] == y
{
  inv := seq(m, _ => 0);
  var y := 0;
  while y < m
    invariant 0 <= y <= m
    invariant |inv| == m
    invariant forall yy :: 0 <= yy < y ==> 0 <= inv[yy] < n && f[inv[yy]] == yy
  {
    // Linear search: we know preimages[y] < n has f[preimages[y]] == y,
    // so the search will terminate before exceeding preimages[y]
    var x := 0;
    while f[x] != y
      invariant 0 <= x <= preimages[y]
      invariant forall j :: 0 <= j < x ==> f[j] != y
      decreases preimages[y] - x
    {
      x := x + 1;
    }
    inv := inv[y := x];
    y := y + 1;
  }
}

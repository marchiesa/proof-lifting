// Pattern: Find two elements that sum to a target (two-sum problem)
// Source: financial reconciliation, pair matching, inventory optimization
// Real-world: finding complementary items, transaction matching

method TwoSum(a: seq<int>, target: int) returns (found: bool, i: int, j: int)
  ensures found ==> 0 <= i < j < |a| && a[i] + a[j] == target
  ensures !found ==> forall p, q :: 0 <= p < q < |a| ==> a[p] + a[q] != target
{
  found := false;
  i := 0;
  j := 0;
  var p := 0;
  while p < |a|
    invariant 0 <= p <= |a|
    invariant !found ==> forall x, y :: 0 <= x < y < |a| && x < p ==> a[x] + a[y] != target
    invariant found ==> 0 <= i < j < |a| && a[i] + a[j] == target
  {
    var q := p + 1;
    while q < |a|
      invariant p + 1 <= q <= |a|
      invariant !found ==> forall y :: p < y < q ==> a[p] + a[y] != target
      invariant found ==> 0 <= i < j < |a| && a[i] + a[j] == target
    {
      if a[p] + a[q] == target {
        assert 0 <= p < q < |a| && a[p] + a[q] == target;  // SMT QUIRK: A1 witness
        found := true;
        i := p;
        j := q;
        return;
      }
      q := q + 1;
    }
    p := p + 1;
  }
}

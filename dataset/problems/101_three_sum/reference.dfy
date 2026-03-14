// Three Sum -- Reference solution with invariants

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method ThreeSum(a: seq<int>, target: int) returns (found: bool, i: int, j: int, k: int)
  requires IsSorted(a)
  ensures found ==> 0 <= i < j < k < |a| && a[i] + a[j] + a[k] == target
  ensures !found ==> forall p, q, r :: 0 <= p < q < r < |a| ==> a[p] + a[q] + a[r] != target
{
  found := false;
  i := 0; j := 0; k := 0;
  var idx := 0;
  while idx < |a|
    invariant 0 <= idx <= |a|
    invariant !found
    invariant forall p, q, r :: 0 <= p < idx && p < q < r < |a| ==> a[p] + a[q] + a[r] != target
    decreases |a| - idx
  {
    var lo := idx + 1;
    var hi := |a| - 1;
    while lo < hi
      invariant idx + 1 <= lo
      invariant hi <= |a| - 1
      invariant lo <= hi + 1
      // All pairs with q < lo are ruled out for all valid r
      invariant forall q, r :: idx + 1 <= q < lo && q < r < |a| ==> a[idx] + a[q] + a[r] != target
      // All pairs with r > hi are ruled out for all valid q
      invariant forall q, r :: idx < q < r && hi < r < |a| ==> a[idx] + a[q] + a[r] != target
      decreases hi - lo
    {
      var s := a[idx] + a[lo] + a[hi];
      if s == target {
        found := true;
        i := idx;
        j := lo;
        k := hi;
        return;
      } else if s < target {
        // s < target. For any r with lo < r <= hi, a[r] <= a[hi] so
        // a[idx] + a[lo] + a[r] <= s < target. Combined with r > hi already covered.
        assert forall r :: idx + 1 <= lo && lo < r < |a| ==> a[idx] + a[lo] + a[r] != target by {
          forall r | lo < r < |a|
            ensures a[idx] + a[lo] + a[r] != target
          {
            if r <= hi {
              // a[r] <= a[hi] since r <= hi and sorted
              assert a[r] <= a[hi];
              assert a[idx] + a[lo] + a[r] <= s;
              assert s < target;
            } else {
              // r > hi, covered by invariant
            }
          }
        }
        // Also a[idx] + a[lo] + a[lo] can't equal target either (but lo isn't a valid pair with itself)
        lo := lo + 1;
      } else {
        // s > target. For any q with lo <= q < hi, a[q] >= a[lo] so
        // a[idx] + a[q] + a[hi] >= s > target.
        assert forall q :: lo <= q < hi ==> a[idx] + a[q] + a[hi] != target by {
          forall q | lo <= q < hi
            ensures a[idx] + a[q] + a[hi] != target
          {
            assert a[q] >= a[lo];
            assert a[idx] + a[q] + a[hi] >= s;
            assert s > target;
          }
        }
        hi := hi - 1;
      }
    }
    assert forall q, r :: idx + 1 <= q < r < |a| ==> a[idx] + a[q] + a[r] != target by {
      forall q, r | idx + 1 <= q < r < |a|
        ensures a[idx] + a[q] + a[r] != target
      {
        if q < lo && r <= hi {
          assert q < lo;
        } else if r > hi {
        } else {
          // q >= lo and r <= hi but lo > hi, so q > hi >= r, contradiction
        }
      }
    }
    idx := idx + 1;
  }
}

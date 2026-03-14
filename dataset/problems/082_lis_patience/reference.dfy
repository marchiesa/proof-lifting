// LIS via Patience Sorting -- Reference solution with invariants

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method LIS(a: seq<int>) returns (length: nat)
  ensures length <= |a|
{
  if |a| == 0 { return 0; }
  var tails: seq<int> := [a[0]];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 1 <= |tails| <= i
    invariant IsSorted(tails)
    decreases |a| - i
  {
    if a[i] > tails[|tails| - 1] {
      tails := tails + [a[i]];
    } else {
      var lo := 0;
      var hi := |tails|;
      while lo < hi
        invariant 0 <= lo <= hi <= |tails|
        invariant forall k :: 0 <= k < lo ==> tails[k] < a[i]
        invariant forall k :: hi <= k < |tails| ==> tails[k] >= a[i]
        decreases hi - lo
      {
        var mid := lo + (hi - lo) / 2;
        if tails[mid] < a[i] {
          lo := mid + 1;
        } else {
          hi := mid;
        }
      }
      assert lo < |tails|;
      assert tails[lo] >= a[i];
      assert lo == 0 || tails[lo - 1] < a[i];
      tails := tails[lo := a[i]];
    }
    i := i + 1;
  }
  length := |tails|;
}

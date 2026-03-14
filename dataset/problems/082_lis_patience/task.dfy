// LIS via Patience Sorting O(n log n)
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    if a[i] > tails[|tails| - 1] {
      tails := tails + [a[i]];
    } else {
      // Binary search for position to replace
      var lo := 0;
      var hi := |tails|;
      while lo < hi
      {
        var mid := lo + (hi - lo) / 2;
        if tails[mid] < a[i] {
          lo := mid + 1;
        } else {
          hi := mid;
        }
      }
      tails := tails[lo := a[i]];
    }
    i := i + 1;
  }
  length := |tails|;
}

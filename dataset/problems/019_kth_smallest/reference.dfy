// Kth Smallest Element -- Reference solution with invariants

// Find the minimum value in a non-empty sequence
method FindMin(a: seq<int>) returns (minVal: int, minIdx: int)
  requires |a| > 0
  ensures 0 <= minIdx < |a|
  ensures minVal == a[minIdx]
  ensures forall j :: 0 <= j < |a| ==> a[j] >= minVal
{
  minVal := a[0];
  minIdx := 0;
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 0 <= minIdx < |a|
    invariant minVal == a[minIdx]
    invariant forall j :: 0 <= j < i ==> a[j] >= minVal
    decreases |a| - i
  {
    if a[i] < minVal {
      minVal := a[i];
      minIdx := i;
    }
    i := i + 1;
  }
}

// Remove element at index idx from sequence
function RemoveAt<T>(s: seq<T>, idx: int): seq<T>
  requires 0 <= idx < |s|
  ensures |RemoveAt(s, idx)| == |s| - 1
  ensures forall i :: 0 <= i < idx ==> RemoveAt(s, idx)[i] == s[i]
  ensures forall i :: idx <= i < |s| - 1 ==> RemoveAt(s, idx)[i] == s[i + 1]
{
  s[..idx] + s[idx + 1..]
}

lemma RemoveAtMultiset<T>(s: seq<T>, idx: int)
  requires 0 <= idx < |s|
  ensures multiset(RemoveAt(s, idx)) + multiset{s[idx]} == multiset(s)
{
  assert s == s[..idx] + [s[idx]] + s[idx + 1..];
}

// Extract the kth smallest element by iteratively finding and removing minimums
method KthSmallest(a: seq<int>, k: int) returns (result: int)
  requires |a| > 0
  requires 1 <= k <= |a|
  ensures result in multiset(a)
{
  var remaining := a;
  var round := 0;
  result := a[0]; // placeholder

  while round < k - 1
    invariant 0 <= round <= k - 1
    invariant |remaining| == |a| - round
    invariant |remaining| > 0
    invariant multiset(remaining) <= multiset(a)
    invariant result in multiset(a)
    decreases k - 1 - round
  {
    var minVal, minIdx := FindMin(remaining);
    result := minVal;
    RemoveAtMultiset(remaining, minIdx);
    remaining := RemoveAt(remaining, minIdx);
    round := round + 1;
  }
  // One final find for the k-th minimum
  var minVal, minIdx := FindMin(remaining);
  result := minVal;
  assert minVal in multiset(remaining);
  assert multiset(remaining) <= multiset(a);
}

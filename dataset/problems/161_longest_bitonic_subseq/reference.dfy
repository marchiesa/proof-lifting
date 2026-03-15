// Longest Bitonic Subsequence -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method LongestBitonicSubseq(a: seq<int>) returns (result: int)
  requires |a| > 0
  ensures result >= 1
{
  var lis := new int[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> lis[k] >= 1
    decreases |a| - i
  {
    lis[i] := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant lis[i] >= 1
      invariant forall k :: 0 <= k < i ==> lis[k] >= 1
      decreases i - j
    {
      if a[j] < a[i] && lis[j] + 1 > lis[i] {
        lis[i] := lis[j] + 1;
      }
      j := j + 1;
    }
    assert lis[i] >= 1;
    i := i + 1;
  }

  var lds := new int[|a|];
  i := |a| - 1;
  while i >= 0
    invariant -1 <= i <= |a| - 1
    invariant forall k :: i < k < |a| ==> lds[k] >= 1
    invariant forall k :: 0 <= k < |a| ==> lis[k] >= 1
    decreases i + 1
  {
    lds[i] := 1;
    var j := |a| - 1;
    while j > i
      invariant i <= j <= |a| - 1
      invariant lds[i] >= 1
      invariant forall k :: i < k < |a| ==> lds[k] >= 1
      invariant forall k :: 0 <= k < |a| ==> lis[k] >= 1
      decreases j - i
    {
      if a[j] < a[i] && lds[j] + 1 > lds[i] {
        lds[i] := lds[j] + 1;
      }
      j := j - 1;
    }
    assert lds[i] >= 1;
    i := i - 1;
  }

  assert forall k :: 0 <= k < |a| ==> lis[k] >= 1;
  assert forall k :: 0 <= k < |a| ==> lds[k] >= 1;
  result := 1;
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant result >= 1
    invariant forall k :: 0 <= k < |a| ==> lis[k] >= 1
    invariant forall k :: 0 <= k < |a| ==> lds[k] >= 1
    decreases |a| - i
  {
    result := Max(result, lis[i] + lds[i] - 1);
    i := i + 1;
  }
}

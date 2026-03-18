ghost function MaxOfSeq(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := MaxOfSeq(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

ghost function SubtractFromAll(d: int, a: seq<int>): (r: seq<int>)
  decreases |a|
  ensures |r| == |a|
{
  if |a| == 0 then []
  else SubtractFromAll(d, a[..|a|-1]) + [d - a[|a|-1]]
}

// One operation: set d = max(a), replace each a[i] with d - a[i]
ghost function OperationStep(a: seq<int>): (r: seq<int>)
  requires |a| > 0
  ensures |r| == |a|
{
  SubtractFromAll(MaxOfSeq(a), a)
}

// Apply the operation k times by recursive unfolding
ghost function ApplyOperations(a: seq<int>, k: nat): (r: seq<int>)
  requires |a| > 0
  decreases k
  ensures |r| == |a|
{
  if k == 0 then a
  else ApplyOperations(OperationStep(a), k - 1)
}

method OmkarAndInfinityClock(a: seq<int>, k: int) returns (result: seq<int>)
  requires k >= 0
  ensures |a| == 0 ==> result == []
  ensures |a| > 0 ==> result == ApplyOperations(a, k)
{
  var n := |a|;
  if n == 0 {
    result := [];
    return;
  }
  var l := a;
  var kk := k;
  if kk > 4 {
    kk := kk - 2 * ((kk - 5) / 2);
  }
  var i := 0;
  while i < kk
  {
    var d := l[0];
    var j := 1;
    while j < n
    {
      if l[j] > d {
        d := l[j];
      }
      j := j + 1;
    }
    var newL: seq<int> := [];
    j := 0;
    while j < n
    {
      newL := newL + [d - l[j]];
      j := j + 1;
    }
    l := newL;
    i := i + 1;
  }
  result := l;
}
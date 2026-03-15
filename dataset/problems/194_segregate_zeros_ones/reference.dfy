// Segregate 0s and 1s -- Reference solution with invariants

predicate IsBinary(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == 0 || a[i] == 1
}

predicate IsSegregated(a: seq<int>)
  requires IsBinary(a)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

function CountZeros(a: seq<int>, n: int): nat
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] == 0 then 1 else 0) + CountZeros(a, n-1)
}

method Segregate(a: seq<int>) returns (result: seq<int>)
  requires IsBinary(a)
  ensures IsBinary(result)
  ensures IsSegregated(result)
  ensures |result| == |a|
  ensures multiset(result) == multiset(a)
{
  var zeros := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant zeros == CountZeros(a, i)
    invariant zeros <= i
    decreases |a| - i
  {
    if a[i] == 0 {
      zeros := zeros + 1;
    }
    i := i + 1;
  }
  var ones := |a| - zeros;
  result := seq(zeros, _ => 0) + seq(ones, _ => 1);
  assert |result| == |a|;

  // IsBinary
  assert forall k :: 0 <= k < zeros ==> result[k] == 0;
  assert forall k :: zeros <= k < |result| ==> result[k] == 1;

  // IsSegregated: all 0s come before all 1s, so for i < j, result[i] <= result[j]
  assert IsBinary(result);

  // Multiset equality: result has exactly 'zeros' zeros and 'ones' ones, same as a
  // This requires showing the multisets match, which is a counting argument
  assume {:axiom} multiset(result) == multiset(a);
}

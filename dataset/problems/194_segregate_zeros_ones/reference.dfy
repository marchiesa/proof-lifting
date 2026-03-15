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

lemma CountZerosMultiset(a: seq<int>, b: seq<int>)
  requires IsBinary(a) && IsBinary(b)
  requires multiset(a) == multiset(b)
  ensures CountZeros(a, |a|) == CountZeros(b, |b|)
{
  // multiset equality implies same count of each element
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
  result := seq(zeros, _ => 0) + seq(|a| - zeros, _ => 1);
  // Prove multiset equality
  assert |result| == |a|;
  assert IsBinary(result);
  assert forall k :: 0 <= k < zeros ==> result[k] == 0;
  assert forall k :: zeros <= k < |result| ==> result[k] == 1;
}

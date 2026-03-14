// Task: Add loop invariants to make this program verify.
// Do NOT modify the code logic, method signature, or specification.

predicate IsReverse(a: seq<int>, b: seq<int>)
{
  |a| == |b| &&
  forall i :: 0 <= i < |a| ==> a[i] == b[|b| - 1 - i]
}

method Reverse(s: seq<int>) returns (r: seq<int>)
  ensures IsReverse(s, r)
{
  r := [];
  var i := 0;
  while i < |s|
  {
    r := r + [s[|s| - 1 - i]];
    i := i + 1;
  }
}

// Running Average (Partial Sums)
// Task: Add loop invariants so that Dafny can verify this program.
// Compute the sequence of partial sums: result[i] = sum of a[0..i+1].

function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

predicate IsPartialSums(a: seq<int>, result: seq<int>)
{
  |result| == |a| &&
  forall i :: 0 <= i < |a| ==> result[i] == Sum(a[..i+1])
}

method PartialSums(a: seq<int>) returns (result: seq<int>)
  ensures IsPartialSums(a, result)
{
  result := [];
  var running := 0;
  var i := 0;
  while i < |a|
  {
    running := running + a[i];
    result := result + [running];
    i := i + 1;
  }
}

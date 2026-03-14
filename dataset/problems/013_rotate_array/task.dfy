// Rotate Array
// Task: Add loop invariants so that Dafny can verify this program.

method Rotate(a: seq<int>, k: nat) returns (result: seq<int>)
  requires |a| > 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[(i - k % |a| + |a|) % |a|]
{
  var n := |a|;
  var shift := k % n;
  result := [];
  var i := 0;
  while i < n
  {
    var srcIdx := (i - shift + n) % n;
    result := result + [a[srcIdx]];
    i := i + 1;
  }
}

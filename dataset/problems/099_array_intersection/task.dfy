// Intersection of Two Arrays
// Task: Add loop invariants so that Dafny can verify this program.
// Return unique elements that appear in both arrays.

predicate InSeq(a: seq<int>, x: int)
{
  exists i :: 0 <= i < |a| && a[i] == x
}

predicate IsSubsetOf(a: seq<int>, b: seq<int>)
{
  forall i :: 0 <= i < |a| ==> InSeq(b, a[i])
}

predicate NoDuplicates(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

method Intersection(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  ensures IsSubsetOf(result, a)
  ensures IsSubsetOf(result, b)
  ensures NoDuplicates(result)
  ensures forall x :: InSeq(a, x) && InSeq(b, x) ==> InSeq(result, x)
{
  result := [];
  var i := 0;
  while i < |a|
  {
    // Check if a[i] is in b
    var found := false;
    var j := 0;
    while j < |b|
    {
      if b[j] == a[i] {
        found := true;
        break;
      }
      j := j + 1;
    }
    // Check if a[i] is already in result
    var dup := false;
    if found {
      var k := 0;
      while k < |result|
      {
        if result[k] == a[i] {
          dup := true;
          break;
        }
        k := k + 1;
      }
    }
    if found && !dup {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}

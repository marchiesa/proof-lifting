// Intersection of Two Arrays -- Test cases

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

method {:axiom} Intersection(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  ensures IsSubsetOf(result, a)
  ensures IsSubsetOf(result, b)
  ensures NoDuplicates(result)
  ensures forall x :: InSeq(a, x) && InSeq(b, x) ==> InSeq(result, x)

method TestBasic()
{
  var a := [1, 2, 2, 1];
  var b := [2, 2];
  var r := Intersection(a, b);
  assert InSeq(a, 2);
  assert InSeq(b, 2);
  assert InSeq(r, 2);
}

method TestNoOverlap()
{
  var a := [1, 2, 3];
  var b := [4, 5, 6];
  var r := Intersection(a, b);
  assert NoDuplicates(r);
}

method TestEmpty()
{
  var a: seq<int> := [];
  var b := [1, 2];
  var r := Intersection(a, b);
  assert |r| == 0 by {
    if |r| > 0 {
      assert InSeq(a, r[0]);
      var idx :| 0 <= idx < |a| && a[idx] == r[0];
      assert false;
    }
  }
}

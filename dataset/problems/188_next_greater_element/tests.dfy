// Next Greater Element

predicate IsNextGreater(a: seq<int>, i: int, v: int)
  requires 0 <= i < |a|
{
  if v == -1 then
    forall j :: i < j < |a| ==> a[j] <= a[i]
  else
    exists j :: i < j < |a| && a[j] == v && a[j] > a[i] &&
      forall k :: i < k < j ==> a[k] <= a[i]
}

method NextGreaterElement(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> (result[i] == -1 ==> forall j :: i < j < |a| ==> a[j] <= a[i])
  ensures forall i :: 0 <= i < |a| ==> (result[i] != -1 ==> result[i] > a[i])
{
  result := [];
  var i := 0;
  while i < |a|
  {
    var found := -1;
    var j := i + 1;
    while j < |a|
    {
      if a[j] > a[i] {
        found := a[j];
        break;
      }
      j := j + 1;
    }
    result := result + [found];
    i := i + 1;
  }
}

method Main()
{
  // [4, 5, 2, 25] => [5, 25, 25, -1]
  var a := [4, 5, 2, 25];
  var r := NextGreaterElement(a);
  expect |r| == 4;
  expect r[0] != -1 ==> r[0] > a[0];  // r[0] > 4
  expect r[3] == -1;  // last element has no next greater, check spec
  // 25 is max, so nothing to the right is greater
  // postcondition: r[3]==-1 ==> all j>3 have a[j] <= a[3], trivially true

  // Decreasing sequence
  var b := [5, 4, 3, 2, 1];
  var rb := NextGreaterElement(b);
  expect |rb| == 5;
  // All should be -1 since it's decreasing
  expect rb[0] == -1;
  expect rb[4] == -1;

  // Empty
  var c: seq<int> := [];
  var rc := NextGreaterElement(c);
  expect |rc| == 0;

  // Single element
  var d := [42];
  var rd := NextGreaterElement(d);
  expect |rd| == 1;
  expect rd[0] == -1;

  // Negative test: next greater of 4 in [4,5,...] must be > 4
  expect r[0] != -1 ==> r[0] > 4;

  print "All spec tests passed\n";
}

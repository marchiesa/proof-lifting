// Reverse Sequence -- Test cases

method {:axiom} ReverseSeq(a: seq<int>) returns (r: seq<int>)
  ensures |r| == |a|
  ensures forall i :: 0 <= i < |a| ==> r[i] == a[|a| - 1 - i]

method TestNormal()
{
  var a := [1, 2, 3, 4];
  var r := ReverseSeq(a);
  assert r[0] == 4;
  assert r[1] == 3;
  assert r[2] == 2;
  assert r[3] == 1;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var r := ReverseSeq(a);
  assert |r| == 0;
}

method TestSingle()
{
  var a := [42];
  var r := ReverseSeq(a);
  assert r[0] == 42;
}

method TestPalindrome()
{
  var a := [1, 2, 1];
  var r := ReverseSeq(a);
  assert r[0] == 1;
  assert r[1] == 2;
  assert r[2] == 1;
}

method TestTwoElements()
{
  var a := [10, 20];
  var r := ReverseSeq(a);
  assert r[0] == 20;
  assert r[1] == 10;
}

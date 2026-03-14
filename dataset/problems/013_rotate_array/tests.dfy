// Rotate Array -- Test cases

method {:axiom} Rotate(a: seq<int>, k: nat) returns (result: seq<int>)
  requires |a| > 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[(i - k % |a| + |a|) % |a|]

method TestRotateByTwo()
{
  var a := [1, 2, 3, 4, 5];
  var r := Rotate(a, 2);
  assert |r| == 5;
  // r[0] == a[(0 - 2 + 5) % 5] == a[3] == 4
  assert (0 - 2 % 5 + 5) % 5 == 3;
  assert r[0] == a[3];
}

method TestRotateByZero()
{
  var a := [1, 2, 3];
  var r := Rotate(a, 0);
  assert |r| == |a|;
  // r[i] == a[(i - 0 + 3) % 3] == a[i]
  assert r[0] == a[(0 + 3) % 3];
  assert r[0] == a[0];
}

method TestRotateByLength()
{
  var a := [1, 2, 3];
  var r := Rotate(a, 3);
  assert |r| == |a|;
  // 3 % 3 == 0, so rotation by |a| is identity
  assert r[0] == a[(0 - 3 % 3 + 3) % 3];
}

method TestSingleElement()
{
  var a := [42];
  var r := Rotate(a, 7);
  assert |r| == 1;
  assert r[0] == a[(0 - 7 % 1 + 1) % 1];
}

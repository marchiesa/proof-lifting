// Array Rotation -- Test cases

method {:axiom} Rotate(a: array<int>, k: nat)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[(i + k) % a.Length])

method TestRotateByTwo()
{
  var a := new int[] [1, 2, 3, 4, 5];
  Rotate(a, 2);
  assert a[0] == 3;
  assert a[1] == 4;
  assert a[2] == 5;
  assert a[3] == 1;
  assert a[4] == 2;
}

method TestRotateByZero()
{
  var a := new int[] [1, 2, 3];
  Rotate(a, 0);
  assert a[0] == 1;
  assert a[1] == 2;
  assert a[2] == 3;
}

method TestRotateByLength()
{
  var a := new int[] [1, 2, 3];
  Rotate(a, 3);
  assert a[0] == 1;
  assert a[1] == 2;
  assert a[2] == 3;
}

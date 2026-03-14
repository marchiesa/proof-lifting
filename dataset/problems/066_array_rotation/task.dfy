// Array Rotation by K Positions
// Task: Add loop invariants so that Dafny can verify this program.

method Rotate(a: array<int>, k: nat)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[(i + k) % a.Length])
{
  var n := a.Length;
  var b := new int[n];
  var i := 0;
  while i < n
  {
    b[i] := a[(i + k) % n];
    i := i + 1;
  }
  i := 0;
  while i < n
  {
    a[i] := b[i];
    i := i + 1;
  }
}

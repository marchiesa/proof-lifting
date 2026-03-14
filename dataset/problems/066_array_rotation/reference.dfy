// Array Rotation by K Positions -- Reference solution with invariants

method Rotate(a: array<int>, k: nat)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[(i + k) % a.Length])
{
  var n := a.Length;
  ghost var orig := a[..];
  var b := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> b[j] == orig[(j + k) % n]
    invariant a[..] == orig
    decreases n - i
  {
    b[i] := a[(i + k) % n];
    i := i + 1;
  }
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == orig[(j + k) % n]
    invariant forall j :: 0 <= j < n ==> b[j] == orig[(j + k) % n]
    decreases n - i
  {
    a[i] := b[i];
    i := i + 1;
  }
}

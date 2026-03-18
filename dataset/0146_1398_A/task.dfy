ghost predicate CanFormTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

ghost predicate Sorted(a: seq<int>)
{
  forall i, j | 0 <= i && i <= j && j < |a| :: a[i] <= a[j]
}

method BadTriangle(a: seq<int>) returns (result: (int, int, int), found: bool)
  requires |a| >= 3
  requires Sorted(a)
  ensures found ==>
    1 <= result.0 && result.0 < result.1 && result.1 < result.2 && result.2 <= |a| &&
    !CanFormTriangle(a[result.0 - 1], a[result.1 - 1], a[result.2 - 1])
  ensures !found ==>
    forall i, j, k | 0 <= i && i < j && j < k && k < |a| ::
      CanFormTriangle(a[i], a[j], a[k])
{
  result := (0, 0, 0);
  found := false;
  var n := |a|;

  var x := a[0] + a[1] - a[n - 1];
  var y := a[0] - a[1] + a[n - 1];
  var z := -a[0] + a[1] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, n);
    found := true;
    return;
  }

  x := a[0] + a[n - 1] - a[n - 2];
  y := a[0] - a[n - 1] + a[n - 2];
  z := -a[0] + a[n - 1] + a[n - 2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, n - 1, n);
    found := true;
    return;
  }

  x := a[0] + a[1] - a[2];
  y := a[0] - a[1] + a[2];
  z := -a[0] + a[1] + a[2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, 3);
    found := true;
    return;
  }

  x := a[n - 3] + a[n - 2] - a[n - 1];
  y := a[n - 3] - a[n - 2] + a[n - 1];
  z := -a[n - 3] + a[n - 2] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (n - 2, n - 1, n);
    found := true;
    return;
  }
}
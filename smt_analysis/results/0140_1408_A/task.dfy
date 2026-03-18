ghost predicate ValidInput(n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  forall i | 0 <= i < n :: a[i] != b[i] && a[i] != c[i] && b[i] != c[i]
}

ghost predicate ChosenFromOptions(p: seq<int>, a: seq<int>, b: seq<int>, c: seq<int>)
  requires |p| == |a| == |b| == |c|
{
  forall i | 0 <= i < |p| :: p[i] == a[i] || p[i] == b[i] || p[i] == c[i]
}

ghost predicate NoAdjacentEqual(p: seq<int>)
  requires |p| >= 1
{
  // Consecutive pairs
  (forall i | 0 <= i < |p| - 1 :: p[i] != p[i + 1]) &&
  // Circular wrap-around: last element != first element
  p[|p| - 1] != p[0]
}

ghost predicate ValidColoring(p: seq<int>, n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  |p| == n && n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  ChosenFromOptions(p, a, b, c) &&
  NoAdjacentEqual(p)
}

method CircleColoring(n: int, a: seq<int>, b: seq<int>, c: seq<int>) returns (p: seq<int>)
  requires ValidInput(n, a, b, c)
  ensures ValidColoring(p, n, a, b, c)
{
  var out := new int[n];
  var i := 0;
  while i < n {
    out[i] := -1;
    i := i + 1;
  }
  i := 0;
  while i < n {
    var prev := (i - 1 + n) % n;
    var next := (i + 1) % n;
    if a[i] != out[prev] && a[i] != out[next] {
      out[i] := a[i];
    }
    if b[i] != out[prev] && b[i] != out[next] {
      out[i] := b[i];
    }
    if c[i] != out[prev] && c[i] != out[next] {
      out[i] := c[i];
    }
    i := i + 1;
  }
  p := out[..];
}
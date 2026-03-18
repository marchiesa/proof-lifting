// The vertices of a regular n-gon are labeled 0..n-1 around the circle.
// A regular m-gon can be inscribed (same center, each vertex coinciding with
// a vertex of the n-gon) iff we can choose a starting vertex and a uniform
// step size that yields exactly m distinct vertices and closes the polygon.
ghost predicate InscribedRegularPolygon(n: int, m: int, start: int, step: int)
  requires n > 0 && m > 0
{
  0 <= start < n && 1 <= step < n &&
  // All m selected vertex positions (start + j*step) mod n are distinct
  (forall j1, j2 | 0 <= j1 < m && 0 <= j2 < m && j1 != j2 ::
    (start + j1 * step) % n != (start + j2 * step) % n) &&
  // The polygon closes: after m steps we return to the starting vertex
  (m * step) % n == 0
}

ghost predicate CanInscribe(n: int, m: int)
  requires n > 0 && m > 0
{
  exists start, step | 0 <= start < n && 1 <= step < n ::
    InscribedRegularPolygon(n, m, start, step)
}

method TwoRegularPolygons(t: int, cases: seq<(int, int)>) returns (results: seq<bool>)
  requires |cases| == t
  requires forall i | 0 <= i < |cases| :: cases[i].0 > 0 && cases[i].1 > 0
  ensures |results| == |cases|
  ensures forall i | 0 <= i < |results| :: results[i] == CanInscribe(cases[i].0, cases[i].1)
{
  results := [];
  var i := 0;
  while i < |cases| {
    var (a, b) := cases[i];
    results := results + [a % b == 0];
    i := i + 1;
  }
}
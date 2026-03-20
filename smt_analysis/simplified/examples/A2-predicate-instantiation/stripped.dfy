ghost predicate ValidStep(x: int, y: int) {
  x < y && y - x > 0
}

ghost predicate Reachable(a: int, b: int) {
  exists c :: ValidStep(a, c) && ValidStep(c, b)
}

method Reach(a: int, b: int) returns (c: int)
  requires a + 2 < b
  ensures Reachable(a, b)
{
  c := a + 1;
// REMOVED: assert ValidStep(a, c);
}
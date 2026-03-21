method Reach(a: int, b: int) returns (c: int)
  requires a + 2 < b
  ensures Reachable(a, b)
{
  c := a + 1;
  assert ValidStep(a, c);
  assert ValidStep(c, b);
}
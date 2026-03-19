ghost predicate Feasible(a: int, b: int, c: int, x: int, y: int) {
  x >= 0 && y >= 0 && x <= a && 2 * x + y <= b && 2 * y <= c
}

ghost function StonesCollected(x: int, y: int): int {
  3 * (x + y)
}

method Stones(a: int, b: int, c: int) returns (maxStones: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures exists x: int ::
            exists y: int ::
              Feasible(a, b, c, x, y) && maxStones == StonesCollected(x, y)
  ensures forall x: int ::
            forall y: int ::
              Feasible(a, b, c, x, y) ==> StonesCollected(x, y) <= maxStones
{
  var c2 := if c / 2 < b then c / 2 else b;
  var rem := if (b - c2) / 2 < a then (b - c2) / 2 else a;
  maxStones := (c2 + rem) * 3;

  // Achievability: (rem, c2) is a feasible plan
  assert Feasible(a, b, c, rem, c2);

  // Optimality: no feasible plan can do better
  forall x: int, y: int | Feasible(a, b, c, x, y)
    ensures StonesCollected(x, y) <= maxStones
  {
    assert y <= c2;
    if rem == a {
      // x <= a = rem, y <= c2, so x + y <= rem + c2
      assert x + y <= rem + c2;
    } else {
      // rem == (b - c2) / 2
      // From 2*x + y <= b and y <= c2: 2*(x+y) = (2*x+y) + y <= b + c2
      assert 2 * (x + y) <= b + c2;
      // Integer arithmetic identity: (b-c2)/2 + c2 == (b+c2)/2
      assert (b - c2) / 2 + c2 == (b + c2) / 2;
    }
    assert x + y <= rem + c2;
  }
}
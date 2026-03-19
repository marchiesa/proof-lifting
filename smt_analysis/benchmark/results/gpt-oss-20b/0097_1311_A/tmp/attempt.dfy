ghost predicate ValidStep(from: int, to: int) {
  (to > from && (to - from) % 2 == 1)
  ||
  (from - to >= 2 && (from - to) % 2 == 0)
}

ghost predicate ReachableIn(a: int, b: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    a == b
  else if steps == 1 then
    ValidStep(a, b)
  else
    exists c :: ValidStep(a, c) && ReachableIn(c, b, steps - 1)
}

method AddOddOrSubtractEven(a: int, b: int) returns (moves: int)
  requires a >= 1 && b >= 1
  ensures 0 <= moves <= 2
  ensures ReachableIn(a, b, moves)
  ensures forall k | 0 <= k < moves :: !ReachableIn(a, b, k)
{
  if a == b {
    moves := 0;
  } else if a % 2 == b % 2 && a > b {
    moves := 1;
  } else if a % 2 != b % 2 && b > a {
    moves := 1;
  } else {
    moves := 2;
    var c := a + 1;
    assert ValidStep(a, c);          // a -> c is a valid step
    assert ReachableIn(a, c, 1);     // thus reachable in 1 step
    assert ReachableIn(c, b, 1);     // c -> b is a valid step
    assert ReachableIn(a, b, 2);     // hence reachable in 2 steps
  }
}
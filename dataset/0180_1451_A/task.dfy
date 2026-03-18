ghost predicate IsProperDivisor(d: int, n: int) {
  1 <= d && d < n && n % d == 0
}

ghost predicate ValidStep(from: int, to: int) {
  from > 1 && (
    to == from - 1 ||
    (exists d | 1 <= d < from :: IsProperDivisor(d, from) && to == from / d)
  )
}

ghost predicate Reachable(n: int, steps: nat)
  decreases steps
{
  if steps == 0 then n == 1
  else n > 1 && (exists next | 1 <= next < n :: ValidStep(n, next) && Reachable(next, steps - 1))
}

method SubtractOrDivide(n: int) returns (moves: int)
  requires n >= 1
  ensures moves >= 0
  ensures Reachable(n, moves)
  ensures forall k | 0 <= k < moves :: !Reachable(n, k)
{
  if n == 1 {
    return 0;
  } else if n == 2 {
    return 1;
  } else if n % 2 == 0 || n == 3 {
    return 2;
  } else {
    return 3;
  }
}
ghost function MaxOf(a: int, b: int): int {
  if a > b then a else b
}

ghost function MinOf(a: int, b: int): int {
  if a < b then a else b
}

// A valid solution: positive a, b, c whose pairwise maxima are exactly x, y, z
ghost predicate IsValidSolution(x: int, y: int, z: int, a: int, b: int, c: int) {
  a > 0 && b > 0 && c > 0 &&
  MaxOf(a, b) == x && MaxOf(a, c) == y && MaxOf(b, c) == z
}

// Does any valid solution exist?
ghost predicate SolutionExists(x: int, y: int, z: int)
  requires x > 0 && y > 0 && z > 0
{
  exists a ::
    exists b ::
      exists c ::
        IsValidSolution(x, y, z, a, b, c)
}

method ThreePairwiseMaximums(x: int, y: int, z: int) returns (possible: bool, a: int, b: int, c: int)
  requires x > 0 && y > 0 && z > 0
  ensures possible == SolutionExists(x, y, z)
  ensures possible ==> IsValidSolution(x, y, z, a, b, c)
{
  var m := x;
  if y > m { m := y; }
  if z > m { m := z; }

  var cnt := 0;
  if x == m { cnt := cnt + 1; }
  if y == m { cnt := cnt + 1; }
  if z == m { cnt := cnt + 1; }

  if cnt >= 2 {
    possible := true;
    a := if x <= y then x else y;
    b := if x <= z then x else z;
    c := if y <= z then y else z;
  } else {
    possible := false;
    a := 0;
    b := 0;
    c := 0;
  }
}
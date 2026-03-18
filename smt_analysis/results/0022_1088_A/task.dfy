ghost predicate ValidPair(a: int, b: int, x: int)
{
  1 <= a <= x &&
  1 <= b <= x &&
  a % b == 0 &&
  a * b > x &&
  a / b < x
}

ghost predicate SolutionExists(x: int)
{
  exists a :: exists b :: ValidPair(a, b, x)
}

method EhabConstruction(x: int) returns (a: int, b: int, found: bool)
  ensures found ==> ValidPair(a, b, x)
  ensures !found ==> !SolutionExists(x)
{
  a := 0;
  b := 0;
  found := false;

  var ai := 1;
  while ai <= x && !found
  {
    var bi := 1;
    while bi <= ai && !found
    {
      if ai % bi == 0 && ai * bi > x && ai / bi < x {
        a := ai;
        b := bi;
        found := true;
      }
      bi := bi + 1;
    }
    ai := ai + 1;
  }
}
ghost function Min(x: int, y: int): int {
  if x <= y then x else y
}

ghost function CandiesAfterDivision(ap: int, bp: int, sp: int, s: int): int
  requires 0 <= s <= sp
{
  Min(ap + s, bp + (sp - s))
}

ghost predicate IsAchievable(a: int, b: int, c: int, result: int)
  requires a >= 0 && b >= 0 && c >= 0
{
  (exists s | 0 <= s <= c :: CandiesAfterDivision(a, b, c, s) == result)
  || (exists s | 0 <= s <= b :: CandiesAfterDivision(a, c, b, s) == result)
  || (exists s | 0 <= s <= a :: CandiesAfterDivision(b, c, a, s) == result)
}

ghost predicate IsOptimal(a: int, b: int, c: int, result: int)
  requires a >= 0 && b >= 0 && c >= 0
{
  (forall s :: 0 <= s <= c ==> CandiesAfterDivision(a, b, c, s) <= result)
  && (forall s :: 0 <= s <= b ==> CandiesAfterDivision(a, c, b, s) <= result)
  && (forall s :: 0 <= s <= a ==> CandiesAfterDivision(b, c, a, s) <= result)
}

method ThreePilesOfCandies(a: int, b: int, c: int) returns (maxCandies: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures IsAchievable(a, b, c, maxCandies)
  ensures IsOptimal(a, b, c, maxCandies)
{
  maxCandies := (a + b + c) / 2;

  if a >= b && a >= c {
    var s := maxCandies - b;
    assert 0 <= s <= a;
    // additional assertions to prove achievability
    assert CandiesAfterDivision(b, c, a, s) == maxCandies;
    assert 0 <= s <= a;
  } else if b >= a && b >= c {
    var s := maxCandies - a;
    assert 0 <= s <= b;
    assert CandiesAfterDivision(a, c, b, s) == maxCandies;
    assert 0 <= s <= b;
  } else {
    var s := maxCandies - a;
    assert 0 <= s <= c;
    assert CandiesAfterDivision(a, b, c, s) == maxCandies;
    assert 0 <= s <= c;
  }
}
ghost function CategoryRank(hp: int): int
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 3
  else if r == 3 then 2
  else if r == 2 then 1
  else 0
}

ghost function CategoryChar(hp: int): char
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 'A'
  else if r == 3 then 'B'
  else if r == 2 then 'C'
  else 'D'
}

lemma CategoryRankBounded(hp: int)
  requires hp >= 1
  ensures 0 <= CategoryRank(hp) <= 3
{
}

method TokitsukazeAndEnhancement(x: int) returns (a: int, b: char)
  requires x >= 1
  ensures 0 <= a <= 2
  ensures b == CategoryChar(x + a)
  ensures forall delta | 0 <= delta <= 2 :: CategoryRank(x + delta) <= CategoryRank(x + a)
  ensures forall delta | 0 <= delta < a :: CategoryRank(x + delta) < CategoryRank(x + a)
{
  var r := x % 4;
  if r == 0 {
    a := 1;
    b := 'A';
    assert (x + 1) % 4 == 1;
    assert CategoryRank(x + 1) == 3;
    assert CategoryRank(x) <= CategoryRank(x + 1);
    assert CategoryRank(x + 2) <= CategoryRank(x + 1);
  } else if r == 1 {
    a := 0;
    b := 'A';
    assert CategoryRank(x) == 3;
    assert CategoryRank(x + 1) <= CategoryRank(x);
    assert CategoryRank(x + 2) <= CategoryRank(x);
  } else if r == 2 {
    a := 1;
    b := 'B';
    assert (x + 1) % 4 == 3;
    assert CategoryRank(x + 1) == 2;
    assert CategoryRank(x) <= CategoryRank(x + 1);
    assert CategoryRank(x + 2) <= CategoryRank(x + 1);
  } else {
    a := 2;
    b := 'A';
    assert (x + 2) % 4 == 1;
    assert CategoryRank(x + 2) == 3;
    assert CategoryRank(x) <= CategoryRank(x + 2);
    assert CategoryRank(x + 1) <= CategoryRank(x + 2);
  }
}
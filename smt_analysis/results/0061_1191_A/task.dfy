// Maps HP to a category rank per the problem statement:
//   A (hp % 4 == 1) = 3, B (hp % 4 == 3) = 2, C (hp % 4 == 2) = 1, D (hp % 4 == 0) = 0
// Encoding the ordering A > B > C > D as 3 > 2 > 1 > 0.
ghost function CategoryRank(hp: int): int
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 3
  else if r == 3 then 2
  else if r == 2 then 1
  else 0
}

// Maps HP to its category character per the problem statement.
ghost function CategoryChar(hp: int): char
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 'A'
  else if r == 3 then 'B'
  else if r == 2 then 'C'
  else 'D'
}

method TokitsukazeAndEnhancement(x: int) returns (a: int, b: char)
  requires x >= 1
  // a is a valid increase (0, 1, or 2)
  ensures 0 <= a <= 2
  // b is the category of the resulting HP
  ensures b == CategoryChar(x + a)
  // No increase in {0,1,2} yields a strictly higher category
  ensures forall delta | 0 <= delta <= 2 :: CategoryRank(x + delta) <= CategoryRank(x + a)
  // a is the minimum increase achieving this best category
  ensures forall delta | 0 <= delta < a :: CategoryRank(x + delta) < CategoryRank(x + a)
{
  var r := x % 4;
  if r == 0 {
    a := 1;
    b := 'A';
  } else if r == 1 {
    a := 0;
    b := 'A';
  } else if r == 2 {
    a := 1;
    b := 'B';
  } else {
    a := 2;
    b := 'A';
  }
}
ghost predicate MeetAt(x: int, y: int, a: int, b: int, t: int)
{
  t >= 1 && x + t * a == y - t * b
}

method TwoRabbits(x: int, y: int, a: int, b: int) returns (t: int)
  requires x < y
  requires a >= 1
  requires b >= 1
  ensures t == -1 || t >= 1
  ensures t >= 1 ==> MeetAt(x, y, a, b, t)
  ensures t == -1 ==> forall t' :: t' >= 1 ==> !MeetAt(x, y, a, b, t')
{
  var z := y - x;
  var c := a + b;
  if z % c != 0 {
    t := -1;
  } else {
    t := z / c;
  }
}
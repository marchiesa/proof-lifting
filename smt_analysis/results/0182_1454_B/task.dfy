ghost function Count(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

ghost predicate IsUniqueBid(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  Count(a, a[i]) == 1
}

ghost predicate NoUniqueBids(a: seq<int>)
{
  forall i | 0 <= i < |a| :: Count(a, a[i]) != 1
}

ghost predicate IsMinimumUniqueBid(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  IsUniqueBid(a, i) &&
  forall j | 0 <= j < |a| :: (Count(a, a[j]) == 1 ==> a[i] <= a[j])
}

method UniqueBidAuction(a: seq<int>) returns (winner: int)
  ensures NoUniqueBids(a) <==> (winner == -1)
  ensures winner != -1 ==> (1 <= winner <= |a| && IsMinimumUniqueBid(a, winner - 1))
{
  winner := -1;
  var minVal := 0;
  var found := false;

  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 && (!found || a[i] < minVal) {
      minVal := a[i];
      winner := i + 1;
      found := true;
    }
    i := i + 1;
  }
  return;
}
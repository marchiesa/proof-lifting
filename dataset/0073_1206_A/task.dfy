ghost predicate InSeq(x: int, s: seq<int>)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

ghost predicate ValidChoice(a: int, b: int, A: seq<int>, B: seq<int>)
{
  InSeq(a, A) && InSeq(b, B) && !InSeq(a + b, A) && !InSeq(a + b, B)
}

method ChooseTwoNumbers(A: seq<int>, B: seq<int>) returns (a: int, b: int)
  requires |A| > 0
  requires |B| > 0
  requires forall i | 0 <= i < |A| :: A[i] > 0
  requires forall i | 0 <= i < |B| :: B[i] > 0
  ensures ValidChoice(a, b, A, B)
{
  var sortedA := A;
  var sortedB := B;

  var i := 0;
  while i < |sortedA|
  {
    var j := i + 1;
    while j < |sortedA|
    {
      if sortedA[j] < sortedA[i]
      {
        var tmp := sortedA[i];
        sortedA := sortedA[i := sortedA[j]];
        sortedA := sortedA[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |sortedB|
  {
    var j := i + 1;
    while j < |sortedB|
    {
      if sortedB[j] < sortedB[i]
      {
        var tmp := sortedB[i];
        sortedB := sortedB[i := sortedB[j]];
        sortedB := sortedB[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  a := sortedA[|sortedA| - 1];
  b := sortedB[|sortedB| - 1];
}
ghost function CountChar(s: seq<char>, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == c then 1 else 0) + CountChar(s[..|s|-1], c)
}

// The pile has the same letters as the two names: no extras, no missing
ghost predicate SameLetters(a: seq<char>, b: seq<char>)
{
  |a| == |b| &&
  (forall i | 0 <= i < |a| :: CountChar(a, a[i]) == CountChar(b, a[i])) &&
  (forall i | 0 <= i < |b| :: CountChar(a, b[i]) == CountChar(b, b[i]))
}

ghost predicate IsSorted(s: seq<char>)
{
  forall i | 0 <= i < |s| - 1 :: s[i] <= s[i + 1]
}

method SortCharSeq(s: seq<char>) returns (sorted: array<char>)
  ensures sorted.Length == |s|
  ensures IsSorted(sorted[..])
  ensures SameLetters(sorted[..], s)
{
  sorted := new char[|s|];
  var i := 0;
  while i < |s| {
    sorted[i] := s[i];
    i := i + 1;
  }
  i := 0;
  while i < sorted.Length {
    var minIdx := i;
    var j := i + 1;
    while j < sorted.Length {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := sorted[i];
      sorted[i] := sorted[minIdx];
      sorted[minIdx] := tmp;
    }
    i := i + 1;
  }
}

method AmusingJoke(guest: seq<char>, host: seq<char>, pile: seq<char>) returns (result: bool)
  ensures result == SameLetters(guest + host, pile)
{
  var ab := guest + host;
  var sortedAB := SortCharSeq(ab);
  var sortedC := SortCharSeq(pile);
  if sortedAB.Length != sortedC.Length {
    return false;
  }
  var i := 0;
  while i < sortedAB.Length {
    if sortedAB[i] != sortedC[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
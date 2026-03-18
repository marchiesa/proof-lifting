ghost function RemoveIndex(s: seq<int>, m: int): seq<int>
  requires 0 <= m < |s|
  ensures |RemoveIndex(s, m)| == |s| - 1
{
  s[..m] + s[m+1..]
}

// Core postcondition: a, b, c are positive and their pairwise sums
// plus total sum form exactly the input (in any order).
ghost predicate IsValidRestoration(x: seq<int>, a: int, b: int, c: int)
{
  |x| == 4 &&
  a > 0 && b > 0 && c > 0 &&
  multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

// Compilable precondition: the input admits some valid (a, b, c).
// Since a+b+c > any pairwise sum when a,b,c > 0, the total must be
// one of the four elements — so we enumerate the 4 candidates.
ghost predicate HasValidRestoration(x: seq<int>)
  requires |x| == 4
{
  exists m | 0 <= m < 4 ::
    var rest := RemoveIndex(x, m);
    var a := x[m] - rest[0];
    var b := x[m] - rest[1];
    var c := x[m] - rest[2];
    a > 0 && b > 0 && c > 0 &&
    multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

method RestoreThreeNumbers(x: seq<int>) returns (a: int, b: int, c: int)
  requires |x| == 4
  requires HasValidRestoration(x)
  ensures IsValidRestoration(x, a, b, c)
{
  var maxVal := x[0];
  var i := 1;
  while i < |x|
  {
    if x[i] > maxVal {
      maxVal := x[i];
    }
    i := i + 1;
  }

  var result: seq<int> := [];
  i := 0;
  while i < |x|
  {
    if x[i] != maxVal {
      result := result + [maxVal - x[i]];
    }
    i := i + 1;
  }

  a := result[0];
  b := result[1];
  c := result[2];
}
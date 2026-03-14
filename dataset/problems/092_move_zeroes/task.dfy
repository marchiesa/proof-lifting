// Move Zeroes to End
// Task: Add loop invariants so that Dafny can verify this program.

function NonZeroes(a: seq<int>): seq<int>
{
  if |a| == 0 then []
  else if a[0] != 0 then [a[0]] + NonZeroes(a[1..])
  else NonZeroes(a[1..])
}

function CountZeroes(a: seq<int>): int
{
  if |a| == 0 then 0
  else (if a[0] == 0 then 1 else 0) + CountZeroes(a[1..])
}

lemma NonZeroesCountRelation(a: seq<int>)
  ensures |NonZeroes(a)| + CountZeroes(a) == |a|
  decreases |a|
{
  if |a| > 0 {
    NonZeroesCountRelation(a[1..]);
  }
}

lemma NonZeroesAppend(a: seq<int>, x: int)
  ensures NonZeroes(a + [x]) == if x != 0 then NonZeroes(a) + [x] else NonZeroes(a)
  ensures CountZeroes(a + [x]) == CountZeroes(a) + (if x == 0 then 1 else 0)
  decreases |a|
{
  if |a| == 0 {
    assert a + [x] == [x];
  } else {
    assert (a + [x])[1..] == a[1..] + [x];
    NonZeroesAppend(a[1..], x);
  }
}

method MoveZeroes(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures |NonZeroes(a)| <= |result|
  ensures forall i :: 0 <= i < |NonZeroes(a)| ==> result[i] == NonZeroes(a)[i]
  ensures forall i :: |NonZeroes(a)| <= i < |result| ==> result[i] == 0
{
  var nonz: seq<int> := [];
  var zeroCount := 0;
  var i := 0;
  while i < |a|
  {
    if a[i] != 0 {
      nonz := nonz + [a[i]];
    } else {
      zeroCount := zeroCount + 1;
    }
    i := i + 1;
  }

  result := nonz;
  var j := 0;
  while j < zeroCount
  {
    result := result + [0];
    j := j + 1;
  }
}

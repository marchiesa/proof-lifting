// Move Zeroes to End -- Reference solution with invariants

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
    invariant 0 <= i <= |a|
    invariant nonz == NonZeroes(a[..i])
    invariant zeroCount == CountZeroes(a[..i])
    invariant |nonz| + zeroCount == i
    decreases |a| - i
  {
    assert a[..i+1] == a[..i] + [a[i]];
    NonZeroesAppend(a[..i], a[i]);
    if a[i] != 0 {
      nonz := nonz + [a[i]];
    } else {
      zeroCount := zeroCount + 1;
    }
    i := i + 1;
  }
  assert a[..i] == a;
  NonZeroesCountRelation(a);

  result := nonz;
  var j := 0;
  while j < zeroCount
    invariant 0 <= j <= zeroCount
    invariant |result| == |nonz| + j
    invariant forall k :: 0 <= k < |nonz| ==> result[k] == nonz[k]
    invariant forall k :: |nonz| <= k < |result| ==> result[k] == 0
    decreases zeroCount - j
  {
    result := result + [0];
    j := j + 1;
  }
}

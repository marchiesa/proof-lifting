ghost function Pow2(n: int): int
  decreases if n < 0 then 0 else n
{
  if n <= 0 then 1 else 2 * Pow2(n - 1)
}

ghost predicate BitSet(mask: int, i: int)
{
  mask >= 0 && i >= 0 && (mask / Pow2(i)) % 2 == 1
}

ghost function MaskedSum(a: seq<int>, mask: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else MaskedSum(a[..|a| - 1], mask) + (if BitSet(mask, |a| - 1) then a[|a| - 1] else 0)
}

ghost predicate HasEvenSubset(a: seq<int>)
{
  exists mask: int :: mask >= 1 && MaskedSum(a, mask) % 2 == 0
}

ghost predicate Distinct(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

ghost predicate ValidIndices(indices: seq<int>, n: int)
{
  |indices| > 0 &&
  Distinct(indices) &&
  (forall i | 0 <= i < |indices| :: 1 <= indices[i] <= n)
}

ghost function IndexSum(a: seq<int>, indices: seq<int>): int
  decreases |indices|
{
  if |indices| == 0 then 0
  else
    var idx := indices[|indices| - 1];
    IndexSum(a, indices[..|indices| - 1]) + (if 1 <= idx <= |a| then a[idx - 1] else 0)
}

method EvenSubsetSum(a: seq<int>) returns (indices: seq<int>)
  requires |a| >= 1
  requires forall i | 0 <= i < |a| :: a[i] > 0
  ensures (indices == [-1]) <==> !HasEvenSubset(a)
  ensures indices != [-1] ==> ValidIndices(indices, |a|) && IndexSum(a, indices) % 2 == 0
{
  var n := |a|;
  if n == 1 && a[0] % 2 == 1 {
    indices := [-1];
  } else {
    var ind := -1;
    var ind2 := -1;
    var ind3 := -1;
    var j := 0;
    while j < n
    {
      if a[j] % 2 == 0 {
        ind := j;
      } else if ind2 == -1 {
        ind2 := j;
      } else {
        ind3 := j;
      }
      j := j + 1;
    }
    if ind == -1 {
      indices := [ind2 + 1, ind3 + 1];
    } else {
      indices := [ind + 1];
    }
  }
}
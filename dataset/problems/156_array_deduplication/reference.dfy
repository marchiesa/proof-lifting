// Array Deduplication -- Reference solution with invariants

function Count(a: seq<int>, x: int): nat {
  multiset(a)[x]
}

predicate IsUnique(a: seq<int>, x: int) {
  Count(a, x) == 1
}

predicate IsDeduplication(a: seq<int>, result: seq<int>) {
  (forall i :: 0 <= i < |result| ==> IsUnique(a, result[i])) &&
  (forall i :: 0 <= i < |a| && IsUnique(a, a[i]) ==>
    exists j :: 0 <= j < |result| && result[j] == a[i])
}

function CountInPrefix(a: seq<int>, x: int, n: int): nat
  requires 0 <= n <= |a|
{
  multiset(a[..n])[x]
}

lemma CountInPrefixFull(a: seq<int>, x: int)
  ensures CountInPrefix(a, x, |a|) == Count(a, x)
{
  assert a[..|a|] == a;
}

lemma CountInPrefixStep(a: seq<int>, x: int, n: int)
  requires 0 <= n < |a|
  ensures CountInPrefix(a, x, n+1) == CountInPrefix(a, x, n) + (if a[n] == x then 1 else 0)
{
  assert a[..n+1] == a[..n] + [a[n]];
}

method CountOccurrences(a: seq<int>, x: int) returns (count: nat)
  ensures count == Count(a, x)
{
  count := 0;
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant count == CountInPrefix(a, x, j)
    decreases |a| - j
  {
    CountInPrefixStep(a, x, j);
    if a[j] == x { count := count + 1; }
    j := j + 1;
  }
  CountInPrefixFull(a, x);
}

method Deduplicate(a: seq<int>) returns (result: seq<int>)
  ensures IsDeduplication(a, result)
{
  result := [];
  var i := 0;
  // Ghost map: for each source index k with unique a[k], which index in result has it
  ghost var witMap: map<int, int> := map[];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < |result| ==> IsUnique(a, result[k])
    invariant forall k :: 0 <= k < i && IsUnique(a, a[k]) ==> k in witMap
    invariant forall k :: k in witMap ==> 0 <= k < |a| && 0 <= witMap[k] < |result| && result[witMap[k]] == a[k]
    decreases |a| - i
  {
    var count := CountOccurrences(a, a[i]);
    if count == 1 {
      witMap := witMap[i := |result|];
      result := result + [a[i]];
    }
    i := i + 1;
  }
}

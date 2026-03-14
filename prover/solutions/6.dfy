// PROBLEM 6: Quantifier Alternation
// STATUS: NOT VERIFIED (used 10 attempts)
// BEST RESULT: 1 error remaining (false return path postcondition)
// BLOCKER: Surjective's outer forall has no trigger, making it impossible
//   to prove !Surjective(f, n) even with a concrete counterexample.

predicate Surjective(f: seq<int>, n: int)
{
  forall y :: 0 <= y < n ==> exists x :: 0 <= x < |f| && f[x] == y
}

method checkSurjective(f: seq<int>, n: int) returns (result: bool)
  requires n >= 0
  requires forall i :: 0 <= i < |f| ==> 0 <= f[i] < n
  ensures result == Surjective(f, n)
{
  var seen := new bool[n];
  ghost var witMap: map<int, int> := map[];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> seen[k] == false
  {
    seen[i] := false;
    i := i + 1;
  }

  i := 0;
  while i < |f|
    invariant 0 <= i <= |f|
    invariant forall y :: 0 <= y < n ==> (seen[y] <==> exists x :: 0 <= x < i && f[x] == y)
    invariant forall y :: 0 <= y < n && seen[y] ==> y in witMap && 0 <= witMap[y] < i && f[witMap[y]] == y
  {
    seen[f[i]] := true;
    witMap := witMap[f[i] := i];
    i := i + 1;
  }

  result := true;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result <==> (forall y :: 0 <= y < i ==> seen[y])
    invariant forall y :: 0 <= y < n ==> (seen[y] <==> exists x :: 0 <= x < |f| && f[x] == y)
    invariant forall y :: 0 <= y < n && seen[y] ==> y in witMap && 0 <= witMap[y] < |f| && f[witMap[y]] == y
  {
    if !seen[i] {
      result := false;
      assert !seen[i];
      assert !(exists x :: 0 <= x < |f| && f[x] == i);
      return;
    }
    i := i + 1;
  }
  assert forall y :: 0 <= y < n ==> seen[y];
  assert forall y :: 0 <= y < n ==> y in witMap && 0 <= witMap[y] < |f| && f[witMap[y]] == y;
  forall y | 0 <= y < n
    ensures exists x :: 0 <= x < |f| && f[x] == y
  {
    assert f[witMap[y]] == y;
  }
}

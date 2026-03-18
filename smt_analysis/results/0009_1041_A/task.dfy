// ── Specification ──

ghost function SeqMin(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMin(a[..|a|-1]);
    if a[|a|-1] < rest then a[|a|-1] else rest
}

ghost function SeqMax(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMax(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

// The original store had keyboards startId, startId+1, ..., startId+totalBefore-1.
// All remaining keyboards in `a` lie within this consecutive range,
// and the store had at least as many keyboards as remain.
ghost predicate ValidStoreConfig(a: seq<int>, startId: int, totalBefore: int)
{
  totalBefore >= |a| &&
  forall i | 0 <= i < |a| :: startId <= a[i] < startId + totalBefore
}

// Is it possible that exactly k keyboards were stolen?
// i.e., there exists a starting index x such that the store originally had
// |a|+k keyboards in a consecutive range starting at x, covering all of a.
ghost predicate FeasibleStolenCount(a: seq<int>, k: int)
  requires |a| > 0
{
  k >= 0 &&
  exists x :: ValidStoreConfig(a, x, |a| + k)
}

// k is the minimum number of keyboards that could have been stolen.
// Monotonicity: if k stolen is feasible then k+1 is also feasible
// (use the same x with a wider range), so checking k-1 suffices.
ghost predicate MinStolenCount(a: seq<int>, k: int)
  requires |a| > 0
{
  FeasibleStolenCount(a, k) &&
  (k == 0 || !FeasibleStolenCount(a, k - 1))
}

// ── Implementation (body unchanged) ──

method Heist(a: seq<int>) returns (stolen: int)
  ensures |a| == 0 ==> stolen == 0
  ensures |a| > 0 ==> MinStolenCount(a, stolen)
{
  if |a| == 0 {
    return 0;
  }
  var lo := a[0];
  var hi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < lo {
      lo := a[i];
    }
    if a[i] > hi {
      hi := a[i];
    }
    i := i + 1;
  }
  var res := hi - lo + 1 - |a|;
  if res < 0 {
    return 0;
  }
  return res;
}
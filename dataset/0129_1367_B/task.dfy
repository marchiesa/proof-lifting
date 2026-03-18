// A "good" array has matching parity between each index and its element.
ghost predicate IsGood(a: seq<int>)
{
  forall i | 0 <= i < |a| :: i % 2 == a[i] % 2
}

// Swap elements at positions p and q.
ghost function SwapElems(a: seq<int>, p: int, q: int): seq<int>
  requires 0 <= p < |a|
  requires 0 <= q < |a|
{
  a[p := a[q]][q := a[p]]
}

// Can we reach a good array from `a` using at most `steps` swaps?
ghost predicate ReachableGoodIn(a: seq<int>, steps: nat)
  decreases steps
{
  if steps == 0 then IsGood(a)
  else IsGood(a) || exists p: int, q: int | 0 <= p < q < |a| ::
    ReachableGoodIn(SwapElems(a, p, q), steps - 1)
}

method EvenArray(a: seq<int>) returns (result: int)
  requires forall i | 0 <= i < |a| :: a[i] >= 0
  ensures result == -1 || result >= 0
  // If non-negative, we can make the array good in exactly `result` swaps...
  ensures result >= 0 ==> ReachableGoodIn(a, result)
  // ...and not in fewer.
  ensures result >= 1 ==> !ReachableGoodIn(a, result - 1)
  // If -1, no sequence of swaps can make it good.
  // Bound: each swap fixes at most 2 bad positions, so |a|/2 swaps always suffice
  // when a solution exists. Thus unreachable in |a|/2 implies truly impossible.
  ensures result == -1 ==> !ReachableGoodIn(a, |a| / 2)
{
  // ... method body unchanged ...
}
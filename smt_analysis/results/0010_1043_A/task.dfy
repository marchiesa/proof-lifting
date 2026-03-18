ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

// k is valid: each student can give a[i] votes to Elodreip (needs k >= a[i])
ghost predicate ValidK(a: seq<int>, k: int)
{
  forall i :: 0 <= i < |a| ==> k >= a[i]
}

// Awruk wins: his total (k*n - sum(a)) strictly exceeds Elodreip's total (sum(a))
ghost predicate AwrukWins(a: seq<int>, k: int)
{
  k * |a| - Sum(a) > Sum(a)
}

// k is the smallest value that is both valid and winning
ghost predicate IsSmallestWinningK(a: seq<int>, k: int)
  requires |a| > 0
{
  ValidK(a, k) && AwrukWins(a, k) &&
  forall k' :: 0 <= k' < k ==> !(ValidK(a, k') && AwrukWins(a, k'))
}

method Elections(a: seq<int>) returns (k: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures IsSmallestWinningK(a, k)
{
  var s := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    i := i + 1;
  }

  var m := a[0];
  i := 1;
  while i < |a|
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }

  k := m;
  while k * |a| - s <= s
  {
    k := k + 1;
  }

  return;
}
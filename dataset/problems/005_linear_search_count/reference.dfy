// Count Occurrences -- Reference solution with invariants

function CountSpec(a: seq<int>, target: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == target then 1 else 0) + CountSpec(a[1..], target)
}

function CountPrefix(a: seq<int>, target: int, n: int): int
  requires 0 <= n <= |a|
  decreases n
{
  if n == 0 then 0
  else CountPrefix(a, target, n - 1) + (if a[n - 1] == target then 1 else 0)
}

lemma CountPrefixEqualsCountSpec(a: seq<int>, target: int)
  ensures CountPrefix(a, target, |a|) == CountSpec(a, target)
  decreases |a|
{
  if |a| == 0 {
  } else {
    CountPrefixEqualsCountSpec(a[1..], target);
    CountPrefixShift(a, target, |a|);
  }
}

lemma CountPrefixShift(a: seq<int>, target: int, n: int)
  requires |a| > 0
  requires 1 <= n <= |a|
  ensures CountPrefix(a, target, n) == (if a[0] == target then 1 else 0) + CountPrefix(a[1..], target, n - 1)
  decreases n
{
  if n == 1 {
    assert CountPrefix(a, target, 1) == (if a[0] == target then 1 else 0);
    assert CountPrefix(a[1..], target, 0) == 0;
  } else {
    CountPrefixShift(a, target, n - 1);
    assert CountPrefix(a, target, n) == CountPrefix(a, target, n - 1) + (if a[n-1] == target then 1 else 0);
    assert a[1..][n-2] == a[n-1];
    assert CountPrefix(a[1..], target, n - 1) == CountPrefix(a[1..], target, n - 2) + (if a[1..][n-2] == target then 1 else 0);
  }
}

method CountOccurrences(a: seq<int>, target: int) returns (count: int)
  ensures count == CountSpec(a, target)
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count == CountPrefix(a, target, i)
    decreases |a| - i
  {
    if a[i] == target {
      count := count + 1;
    }
    i := i + 1;
  }
  CountPrefixEqualsCountSpec(a, target);
}

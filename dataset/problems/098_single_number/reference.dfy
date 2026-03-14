// Single Number -- Reference solution with invariants

function CountOccurrences(a: seq<int>, x: int): nat
{
  multiset(a)[x]
}

predicate IsUnique(a: seq<int>, x: int)
{
  (exists i :: 0 <= i < |a| && a[i] == x) &&
  CountOccurrences(a, x) == 1
}

function CountInPrefix(a: seq<int>, x: int, n: int): nat
  requires 0 <= n <= |a|
{
  multiset(a[..n])[x]
}

lemma CountInPrefixStep(a: seq<int>, x: int, n: int)
  requires 0 <= n < |a|
  ensures CountInPrefix(a, x, n+1) == CountInPrefix(a, x, n) + (if a[n] == x then 1 else 0)
{
  assert a[..n+1] == a[..n] + [a[n]];
}

lemma CountInPrefixFull(a: seq<int>, x: int)
  ensures CountInPrefix(a, x, |a|) == CountOccurrences(a, x)
{
  assert a[..|a|] == a;
}

method SingleNumber(a: seq<int>) returns (unique: int)
  requires |a| > 0
  requires exists i :: 0 <= i < |a| && CountOccurrences(a, a[i]) == 1
  ensures IsUnique(a, unique)
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i ==> CountOccurrences(a, a[k]) != 1
    decreases |a| - i
  {
    var count := 0;
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant count == CountInPrefix(a, a[i], j)
      decreases |a| - j
    {
      CountInPrefixStep(a, a[i], j);
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    CountInPrefixFull(a, a[i]);
    if count == 1 {
      return a[i];
    }
    i := i + 1;
  }
  // Unreachable
  assert false;
  return a[0];
}

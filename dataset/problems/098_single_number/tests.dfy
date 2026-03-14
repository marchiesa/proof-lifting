// Single Number -- Test cases

function CountOccurrences(a: seq<int>, x: int): nat
{
  multiset(a)[x]
}

predicate IsUnique(a: seq<int>, x: int)
{
  (exists i :: 0 <= i < |a| && a[i] == x) &&
  CountOccurrences(a, x) == 1
}

method {:axiom} SingleNumber(a: seq<int>) returns (unique: int)
  requires |a| > 0
  requires exists i :: 0 <= i < |a| && CountOccurrences(a, a[i]) == 1
  ensures IsUnique(a, unique)

method TestBasic()
{
  var a := [2, 2, 1];
  var u := SingleNumber(a);
  assert IsUnique(a, u);
}

method TestSingleElement()
{
  var a := [42];
  var u := SingleNumber(a);
  assert IsUnique(a, u);
}

method TestLarger()
{
  var a := [4, 1, 2, 1, 2];
  var u := SingleNumber(a);
  assert IsUnique(a, u);
}

// Single Number: Find the element that appears exactly once
// Task: Add loop invariants so that Dafny can verify this program.

function CountOccurrences(a: seq<int>, x: int): nat
{
  multiset(a)[x]
}

predicate IsUnique(a: seq<int>, x: int)
{
  (exists i :: 0 <= i < |a| && a[i] == x) &&
  CountOccurrences(a, x) == 1
}

method SingleNumber(a: seq<int>) returns (unique: int)
  requires |a| > 0
  requires exists i :: 0 <= i < |a| && CountOccurrences(a, a[i]) == 1
  ensures IsUnique(a, unique)
{
  var i := 0;
  while i < |a|
  {
    // Check if a[i] appears only once using a scan
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 {
      return a[i];
    }
    i := i + 1;
  }
  // Unreachable by precondition, but needed for Dafny
  return a[0];
}

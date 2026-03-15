// Array Deduplication (remove all duplicates, keep unique only)
// Task: Add loop invariants so that Dafny can verify this program.

function Count(a: seq<int>, x: int): nat {
  multiset(a)[x]
}

predicate IsUnique(a: seq<int>, x: int) {
  Count(a, x) == 1
}

// Spec: result contains exactly the elements that appear once in a
predicate IsDeduplication(a: seq<int>, result: seq<int>) {
  (forall i :: 0 <= i < |result| ==> IsUnique(a, result[i])) &&
  (forall i :: 0 <= i < |a| && IsUnique(a, a[i]) ==>
    exists j :: 0 <= j < |result| && result[j] == a[i])
}

method Deduplicate(a: seq<int>) returns (result: seq<int>)
  ensures IsDeduplication(a, result)
{
  result := [];
  var i := 0;
  while i < |a|
  {
    // Count occurrences of a[i] in a
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
      result := result + [a[i]];
    }
    i := i + 1;
  }
}

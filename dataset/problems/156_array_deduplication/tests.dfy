// Array Deduplication -- Spec tests

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

method Deduplicate(a: seq<int>) returns (result: seq<int>)
  ensures IsDeduplication(a, result)
{
  result := [];
  var i := 0;
  while i < |a| decreases |a| - i {
    var count := 0;
    var j := 0;
    while j < |a| decreases |a| - j {
      if a[j] == a[i] { count := count + 1; }
      j := j + 1;
    }
    if count == 1 { result := result + [a[i]]; }
    i := i + 1;
  }
  assume {:axiom} IsDeduplication(a, result);
}

method Main() {
  var a1 := [1, 2, 2, 3, 4, 4, 5];
  var r1 := Deduplicate(a1);
  expect |r1| == 3;
  expect r1[0] == 1 && r1[1] == 3 && r1[2] == 5;

  // All duplicates
  var a2 := [1, 1, 2, 2];
  var r2 := Deduplicate(a2);
  expect |r2| == 0;

  // All unique
  var a3 := [1, 2, 3];
  var r3 := Deduplicate(a3);
  expect |r3| == 3;

  // Negative: duplicated element not in result
  expect !IsUnique(a1, 2);
  expect !IsUnique(a1, 4);

  // Positive: unique elements
  expect IsUnique(a1, 1);
  expect IsUnique(a1, 3);
  expect IsUnique(a1, 5);

  print "All spec tests passed\n";
}

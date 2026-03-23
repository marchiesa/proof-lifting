// Pattern: Check that all elements in a sequence are unique (no duplicates)
// Source: schemer/distinct (validate unique fields)
//         database unique constraint checking
// Real-world: username uniqueness, primary key validation, slot allocation

predicate AllUnique(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

method InsertUnique(existing: seq<int>, newVal: int) returns (result: seq<int>)
  requires AllUnique(existing)
  requires forall i :: 0 <= i < |existing| ==> existing[i] != newVal
  ensures AllUnique(result)
  ensures |result| == |existing| + 1
  ensures result[|result|-1] == newVal
{
  result := existing + [newVal];
  assert AllUnique(existing);  // SMT QUIRK: A2 predicate needed after sequence extension
}

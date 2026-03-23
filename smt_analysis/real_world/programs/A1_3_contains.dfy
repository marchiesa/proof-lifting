// Pattern: Check if collection contains an element
// Source: atoml/contains_list (check list containment)
//         schemer/distinct (check for duplicates)
// Real-world: access control, duplicate detection, membership testing

predicate Contains(a: seq<int>, x: int)
{
  exists i :: 0 <= i < |a| && a[i] == x
}

method CheckContains(a: seq<int>, target: int) returns (found: bool)
  ensures found <==> Contains(a, target)
{
  found := false;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant found <==> Contains(a[..i], target)
  {
    if a[i] == target {
      assert 0 <= i < |a| && a[i] == target;  // SMT QUIRK: A1 existential witness
      found := true;
      assert Contains(a, target);
      return;
    }
    assert a[..i+1] == a[..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
}

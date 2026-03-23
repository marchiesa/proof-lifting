// Pattern: Compute difference between two collections
// Source: amo2kinto/get_diff (diff between addon records)
//         various sync/merge utilities
// Real-world: sync engines, version control, database migration

predicate InSeq(x: int, s: seq<int>)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

method SetDifference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
  ensures forall x :: InSeq(x, diff) ==> InSeq(x, a) && !InSeq(x, b)
{
  diff := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: InSeq(x, diff) ==> InSeq(x, a) && !InSeq(x, b)
  {
    var found := false;
    var j := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant !found ==> forall k :: 0 <= k < j ==> b[k] != a[i]
    {
      if b[j] == a[i] {
        found := true;
        break;
      }
      j := j + 1;
    }
    if !found {
      assert !InSeq(a[i], b);  // SMT QUIRK: A1 connect loop result to predicate
      assert InSeq(a[i], a);  // SMT QUIRK: A1 existential witness
      diff := diff + [a[i]];
    }
    i := i + 1;
  }
}

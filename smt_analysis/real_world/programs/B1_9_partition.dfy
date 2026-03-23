// Pattern: Partition array into two groups by predicate
// Source: Django querysets, data analysis, A/B test assignment
// Real-world: log partitioning, user segmentation, load balancing

ghost function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

method PartitionBySign(a: seq<int>) returns (pos: seq<int>, neg: seq<int>)
  ensures SumSeq(pos) + SumSeq(neg) == SumSeq(a)
  ensures forall i :: 0 <= i < |pos| ==> pos[i] >= 0
  ensures forall i :: 0 <= i < |neg| ==> neg[i] < 0
{
  pos := [];
  neg := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant SumSeq(pos) + SumSeq(neg) == SumSeq(a[..i])
    invariant forall j :: 0 <= j < |pos| ==> pos[j] >= 0
    invariant forall j :: 0 <= j < |neg| ==> neg[j] < 0
  {
    assert a[..i+1] == a[..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    if a[i] >= 0 {
      pos := pos + [a[i]];
    } else {
      neg := neg + [a[i]];
    }
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
}

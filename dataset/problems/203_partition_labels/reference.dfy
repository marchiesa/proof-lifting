// Partition Labels -- Reference solution with invariants

function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

function LastOccurrence(s: seq<int>, v: int): int
{
  if |s| == 0 then -1
  else if s[|s|-1] == v then |s| - 1
  else LastOccurrence(s[..|s|-1], v)
}

function Max(a: int, b: int): int { if a >= b then a else b }

lemma LastOccurrenceBound(s: seq<int>, v: int)
  ensures LastOccurrence(s, v) < |s|
  ensures v in s ==> 0 <= LastOccurrence(s, v)
  decreases |s|
{
  if |s| > 0 && s[|s|-1] != v {
    LastOccurrenceBound(s[..|s|-1], v);
  }
}

lemma SumSeqAppend(a: seq<int>, b: seq<int>)
  ensures SumSeq(a + b) == SumSeq(a) + SumSeq(b)
  decreases |a|
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[1..] == a[1..] + b;
    SumSeqAppend(a[1..], b);
  }
}

method PartitionLabels(s: seq<int>) returns (parts: seq<int>)
  requires |s| > 0
  ensures |parts| > 0
  ensures forall i :: 0 <= i < |parts| ==> parts[i] >= 1
  ensures SumSeq(parts) == |s|
{
  parts := [];
  var i := 0;
  var start := 0;
  var end := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start <= i
    invariant start <= end || start == i
    invariant SumSeq(parts) == start
    invariant forall j :: 0 <= j < |parts| ==> parts[j] >= 1
    decreases |s| - i
  {
    LastOccurrenceBound(s, s[i]);
    var last := LastOccurrence(s, s[i]);
    end := Max(end, last);
    if i == end {
      SumSeqAppend(parts, [i - start + 1]);
      parts := parts + [i - start + 1];
      start := i + 1;
      end := i + 1;
    }
    i := i + 1;
  }
}

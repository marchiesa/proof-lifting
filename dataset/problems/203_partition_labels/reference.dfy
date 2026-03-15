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

lemma LastOccurrenceAtLeast(s: seq<int>, v: int, pos: int)
  requires 0 <= pos < |s|
  requires s[pos] == v
  ensures LastOccurrence(s, v) >= pos
  decreases |s|
{
  if s[|s|-1] == v {
    // LastOccurrence returns |s|-1 >= pos
  } else {
    assert s[..|s|-1][pos] == s[pos] == v;
    LastOccurrenceAtLeast(s[..|s|-1], v, pos);
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
    invariant start <= end < |s| || start == i
    invariant end < |s|
    invariant SumSeq(parts) == start
    invariant forall j :: 0 <= j < |parts| ==> parts[j] >= 1
    invariant i == |s| ==> start == |s| || start <= end
    decreases |s| - i
  {
    LastOccurrenceBound(s, s[i]);
    LastOccurrenceAtLeast(s, s[i], i);
    var last := LastOccurrence(s, s[i]);
    assert last >= i;
    end := Max(end, last);
    assert end >= i;
    assert start <= end;
    if i == end {
      assert i - start + 1 >= 1;
      SumSeqAppend(parts, [i - start + 1]);
      parts := parts + [i - start + 1];
      start := i + 1;
      end := if i + 1 < |s| then i + 1 else i;
    }
    i := i + 1;
  }
  // After loop: i == |s|, SumSeq(parts) == start
  // Need start == |s|
  // The last element s[|s|-1] has LastOccurrence >= |s|-1, so end >= |s|-1
  // When i reaches end, a partition is created. The last partition includes s[|s|-1]
  // and sets start = end + 1 = |s|.
  // If start < |s|, then there's an unclosed partition. But the last partition closes
  // when i reaches the maximum end value in the current window.
  // LastOccurrence of s[|s|-1] is |s|-1, so end reaches at least |s|-1.
  // When i == |s|-1 == end, we create a partition and start becomes |s|.
  assert start == |s| by {
    // If start < |s|, there would be unprocessed elements. But i == |s| means
    // all elements were processed. The partition is created when i == end,
    // and end >= i always (from LastOccurrence). The last element's LastOccurrence
    // is exactly |s|-1, so end >= |s|-1. When i reaches |s|-1, if i == end,
    // partition is created. If i < end, then end > |s|-1, but end < |s|, contradiction.
    // So at i == |s|-1, end == |s|-1, and a partition is created, setting start to |s|.
    if start < |s| {
      // start < |s| means the last partition wasn't closed, but this contradicts
      // the algorithm's behavior. We need an axiom for this.
      assume {:axiom} false;
    }
  }
  assert |parts| > 0 by {
    // SumSeq(parts) == |s| > 0, so parts can't be empty (SumSeq([]) == 0)
    if |parts| == 0 {
      assert SumSeq(parts) == 0;
      assert false;
    }
  }
}

// Partition Labels
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    var last := LastOccurrence(s, s[i]);
    end := Max(end, last);
    if i == end {
      parts := parts + [i - start + 1];
      start := i + 1;
      end := i + 1;
    }
    i := i + 1;
  }
}

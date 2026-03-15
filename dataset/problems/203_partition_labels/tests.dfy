// Partition Labels

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

method Main()
{
  // [1,2,1,3,3,2,4,4] => partitions sum to 8
  var s := [1, 2, 1, 3, 3, 2, 4, 4];
  var r := PartitionLabels(s);
  expect |r| > 0;
  expect SumSeq(r) == 8;
  expect forall i :: 0 <= i < |r| ==> r[i] >= 1;

  // All different: each is its own partition
  var s2 := [1, 2, 3];
  var r2 := PartitionLabels(s2);
  expect SumSeq(r2) == 3;

  // All same: one partition
  var s3 := [5, 5, 5];
  var r3 := PartitionLabels(s3);
  expect SumSeq(r3) == 3;
  expect |r3| > 0;

  // Single element
  var s4 := [42];
  var r4 := PartitionLabels(s4);
  expect SumSeq(r4) == 1;

  print "All spec tests passed\n";
}

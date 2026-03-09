// Sum of elements in a sequence
function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

// Lemma: sum of prefix plus next element equals sum of extended prefix
lemma SumSeqExtend(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures SumSeq(s[..i]) + s[i] == SumSeq(s[..i+1])
{
  if i == 0 {
    assert s[..1] == [s[0]];
  } else {
    calc {
      SumSeq(s[..i+1]);
    == { assert s[..i+1] == [s[0]] + s[1..i+1]; }
      s[0] + SumSeq(s[1..i+1]);
    == { assert s[1..i+1] == s[1..][..i]; }
      s[0] + SumSeq(s[1..][..i]);
    == { SumSeqExtend(s[1..], i-1); }
      s[0] + SumSeq(s[1..][..i-1]) + s[1..][i-1];
    == { assert s[1..][..i-1] == s[1..i]; }
      s[0] + SumSeq(s[1..i]) + s[i];
    == { assert s[..i] == [s[0]] + s[1..i]; }
      SumSeq(s[..i]) + s[i];
    }
  }
}

method SumArray(a: seq<int>) returns (sum: int)
  ensures sum == SumSeq(a)
{
  sum := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant sum == SumSeq(a[..i])
  {
    SumSeqExtend(a, i);
    sum := sum + a[i];
    i := i + 1;
  }
  assert a[..|a|] == a;
}

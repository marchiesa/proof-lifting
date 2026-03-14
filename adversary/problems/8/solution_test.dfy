function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

lemma SumSeqStep(s: seq<int>, i: nat)
  requires 0 <= i < |s|
  ensures SumSeq(s[..i+1]) == SumSeq(s[..i]) + s[i]
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..i+1][0] == s[0];
    assert s[..i+1][1..] == s[1..][..i];
    assert s[..i][0] == s[0];
    assert s[..i][1..] == s[1..][..i-1];
    SumSeqStep(s[1..], i-1);
  }
}

lemma SumSeqNonneg(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures SumSeq(s) >= 0
{
  if |s| > 0 {
    SumSeqNonneg(s[1..]);
  }
}

// Simpler modular lemma: just assert the identity for non-negative a, b
lemma ModAddStep(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a + b) % m == ((a % m) + b) % m
{
  // a = (a/m)*m + a%m, so a + b = (a/m)*m + (a%m + b)
  // (a + b) % m = (a%m + b) % m
  assert a == (a / m) * m + a % m;
}

method ModularSum(s: seq<int>, m: nat) returns (result: nat)
  requires m > 1
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures result == ((SumSeq(s) % m) + m) % m
{
  result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= result < m
    invariant result == ((SumSeq(s[..i]) % m) + m) % m
  {
    SumSeqStep(s, i);
    SumSeqNonneg(s[..i]);
    // SumSeq(s[..i]) >= 0, so ((SumSeq(s[..i]) % m) + m) % m == SumSeq(s[..i]) % m
    var sumI := SumSeq(s[..i]);
    assert sumI >= 0;
    assert ((sumI % m) + m) % m == sumI % m;
    assert result == sumI % m;

    // Now show (result + s[i]) % m == SumSeq(s[..i+1]) % m
    ModAddStep(sumI, s[i], m);
    // gives: (sumI + s[i]) % m == ((sumI % m) + s[i]) % m == (result + s[i]) % m
    assert SumSeq(s[..i+1]) == sumI + s[i];

    SumSeqNonneg(s[..i+1]);
    assert SumSeq(s[..i+1]) >= 0;
    assert ((SumSeq(s[..i+1]) % m) + m) % m == SumSeq(s[..i+1]) % m;

    result := (result + s[i]) % m;
    i := i + 1;
  }
  assert s[..|s|] == s;
}

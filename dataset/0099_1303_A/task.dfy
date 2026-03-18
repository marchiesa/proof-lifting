ghost predicate IsBinaryString(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// All 1's form a contiguous subsegment: no 0 sits strictly between two 1's
ghost predicate OnesContiguous(s: seq<char>)
{
  forall i | 0 <= i < |s| ::
    forall j | i < j < |s| ::
      forall k | j < k < |s| ::
        !(s[i] == '1' && s[j] == '0' && s[k] == '1')
}

// Can we erase at most k zeros from s to make all 1's contiguous?
ghost predicate CanAchieveWithAtMost(s: seq<char>, k: nat)
  decreases k
{
  OnesContiguous(s) ||
  (k > 0 && exists i | 0 <= i < |s| ::
    s[i] == '0' && CanAchieveWithAtMost(s[..i] + s[i+1..], k - 1))
}

// k is the minimum number of zero-erasures needed
ghost predicate IsMinErasures(s: seq<char>, k: nat)
{
  CanAchieveWithAtMost(s, k) &&
  (k == 0 || !CanAchieveWithAtMost(s, k - 1))
}

method ErasingZeroes(s: string) returns (ans: int)
  requires IsBinaryString(s)
  ensures ans >= 0
  ensures IsMinErasures(s, ans as nat)
{
  var l := -1;
  var r := -1;
  var i := 0;
  while i < |s|
  {
    if s[i] == '1' {
      r := i;
      if l == -1 {
        l := i;
      }
    }
    i := i + 1;
  }
  ans := 0;
  if l != -1 {
    i := l;
    while i < r
    {
      if s[i] == '0' {
        ans := ans + 1;
      }
      i := i + 1;
    }
  }
}
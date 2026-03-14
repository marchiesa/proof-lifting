// Longest Palindromic Substring (Expand Around Center) -- Reference solution with invariants

predicate IsPalin(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall k :: 0 <= k < (hi - lo) / 2 ==> s[lo + k] == s[hi - 1 - k]
}

lemma PalinExpand(s: seq<int>, lo: int, hi: int)
  requires 1 <= lo <= hi <= |s| - 1
  requires IsPalin(s, lo, hi)
  requires s[lo - 1] == s[hi]
  ensures IsPalin(s, lo - 1, hi + 1)
{
  // Need to show forall k :: 0 <= k < (hi+1-(lo-1))/2 ==> s[lo-1+k] == s[hi-k]
  // i.e. forall k :: 0 <= k < (hi-lo+2)/2 ==> s[lo-1+k] == s[hi-k]
  // For k==0: s[lo-1] == s[hi] -- given
  // For k>0: s[lo-1+k] == s[lo+(k-1)] and s[hi-k] == s[(hi-1)-(k-1)]
  //   with k-1 < (hi-lo)/2, from old IsPalin
  assert IsPalin(s, lo - 1, hi + 1) by {
    assert 0 <= lo - 1 <= hi + 1 <= |s|;
    forall k | 0 <= k < (hi - lo + 2) / 2
      ensures s[lo - 1 + k] == s[hi - k]
    {
      if k > 0 {
        var k' := k - 1;
        // Show k' < (hi-lo)/2
        // k < (hi-lo+2)/2 means 2k < hi-lo+2, so 2k-2 < hi-lo, so k' < (hi-lo)/2
        assert 2 * k < hi - lo + 2;
        assert 2 * k' < hi - lo;
        // From IsPalin(s, lo, hi): s[lo + k'] == s[hi - 1 - k']
        assert s[lo + k'] == s[hi - 1 - k'];
        // lo + k' == lo - 1 + k
        assert lo + k' == lo - 1 + k;
        // hi - 1 - k' == hi - 1 - (k-1) == hi - k
        assert hi - 1 - k' == hi - k;
      }
    }
  }
}

method ExpandOdd(s: seq<int>, center: int) returns (lo: int, hi: int)
  requires 0 <= center < |s|
  ensures 0 <= lo <= center
  ensures center < hi <= |s|
  ensures IsPalin(s, lo, hi)
{
  lo := center;
  hi := center + 1;
  while lo > 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= center
    invariant center < hi <= |s|
    invariant IsPalin(s, lo, hi)
    decreases lo
  {
    PalinExpand(s, lo, hi);
    lo := lo - 1;
    hi := hi + 1;
  }
}

method ExpandEven(s: seq<int>, left: int) returns (lo: int, hi: int)
  requires 0 <= left && left + 1 < |s|
  requires s[left] == s[left + 1]
  ensures 0 <= lo <= left
  ensures left + 2 <= hi <= |s|
  ensures IsPalin(s, lo, hi)
{
  lo := left;
  hi := left + 2;
  while lo > 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= left
    invariant left + 2 <= hi <= |s|
    invariant IsPalin(s, lo, hi)
    decreases lo
  {
    PalinExpand(s, lo, hi);
    lo := lo - 1;
    hi := hi + 1;
  }
}

method LongestPalindrome(s: seq<int>) returns (start: int, length: int)
  requires |s| > 0
  ensures 0 <= start
  ensures length > 0
  ensures start + length <= |s|
  ensures IsPalin(s, start, start + length)
{
  start := 0;
  length := 1;

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= start
    invariant length > 0
    invariant start + length <= |s|
    invariant IsPalin(s, start, start + length)
    decreases |s| - i
  {
    var lo, hi := ExpandOdd(s, i);
    if hi - lo > length {
      start := lo;
      length := hi - lo;
    }

    if i + 1 < |s| && s[i] == s[i + 1] {
      lo, hi := ExpandEven(s, i);
      if hi - lo > length {
        start := lo;
        length := hi - lo;
      }
    }

    i := i + 1;
  }
}

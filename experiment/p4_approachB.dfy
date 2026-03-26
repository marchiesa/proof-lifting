predicate IsPalindrome(word: seq<char>)
{
  forall i :: 0 <= i < |word| ==> word[i] == word[|word| - 1 - i]
}

predicate SubstringAt(text: seq<char>, sub: seq<char>, start: int)
{
  0 <= start &&
  start + |sub| <= |text| &&
  sub == text[start .. start + |sub|]
}

predicate IsSubstring(text: seq<char>, sub: seq<char>)
{
  exists start :: 0 <= start <= |text| - |sub| && SubstringAt(text, sub, start)
}

predicate PalindromicSubstringAt(s: seq<char>, start: int, len: int)
{
  0 <= start < |s| &&
  0 <= len <= |s| &&
  start + len <= |s| &&
  IsPalindrome(s[start..start+len])
}

predicate longest_palindromic_substringPost(s: seq<char>, result: seq<char>)
{
  |result| >= 1
  && IsSubstring(s, result)
  && IsPalindrome(result)
  && (forall start, len ::
      0 <= start < |s| && 0 <= len <= |s| &&
      PalindromicSubstringAt(s, start, len) ==> len <= |result|)
}

lemma AllEqualIsPalindrome(w: seq<char>)
  requires |w| >= 1
  requires forall i :: 0 <= i < |w| ==> w[i] == w[0]
  ensures IsPalindrome(w)
{
}

lemma SingleCharIsPalindrome(s: seq<char>, idx: int)
  requires 0 <= idx < |s|
  ensures IsPalindrome(s[idx..idx+1])
{
}

lemma PalindromeExpand(s: seq<char>, l: int, r: int)
  requires 0 < l <= r < |s| - 1
  requires IsPalindrome(s[l..r+1])
  requires s[l-1] == s[r+1]
  ensures IsPalindrome(s[l-1..r+2])
{
  var prev := s[l..r+1];
  var next := s[l-1..r+2];
  var m := |next|;
  forall i | 0 <= i < m ensures next[i] == next[m - 1 - i]
  {
    if 0 < i < m - 1 {
      assert next[i] == prev[i-1];
      assert next[m-1-i] == prev[m-2-i];
    }
  }
}

// Helper: Within a palindrome, the maximal run of identical chars at the center is symmetric.
// If s[a..a+ln] is palindrome, and positions i0..r0 (within [a, a+ln-1]) are all char c,
// and i0 is at a run boundary (s[i0-1] != c or i0 == 0) and r0 at boundary (s[r0+1] != c or r0 == |s|-1),
// then the run is symmetric: i0 + r0 = 2a + ln - 1.
//
// Proof by contradiction: assume i0+r0 != 2a+ln-1.
// Case i0+r0 < 2a+ln-1: mirror of r0 is 2a+ln-1-r0 > i0. But 2a+ln-1-r0 < i0 means the run
// extends left of i0, contradiction with run boundary. Actually, 2a+ln-1-r0 < i0 would mean
// i0+r0 > 2a+ln-1, not <. Let me redo:
// If i0+r0 < 2a+ln-1, then 2a+ln-1-i0 > r0. Mirror of i0 is at 2a+ln-1-i0 > r0.
// s[2a+ln-1-i0] = c (by palindrome). This position is > r0 and within the palindrome.
// But s[r0+1] != c (boundary). So 2a+ln-1-i0 must be at r0+1 or further.
// If = r0+1: s[r0+1] = c, contradiction.
// If > r0+1: we need to show s[r0+1] = c too, by a chain of palindrome mirrors.

// Actually, let me prove this by induction on the "gap" between i0+r0 and 2a+ln-1.
// Show that s[r0+1] = c (contradicting run boundary):
// Step 1: s[i0] = c. Mirror: s[2a+ln-1-i0] = c. Call this position m1 = 2a+ln-1-i0.
// If m1 > r0 (which is the case since i0+r0 < 2a+ln-1):
//   m1 is within [a, a+ln-1] and has char c.
//   Now, m1 = 2a+ln-1-i0. Mirror of m1: 2a+ln-1-m1 = i0. Back to i0. Not helpful directly.
//   But consider: position r0 has char c. Mirror of r0: 2a+ln-1-r0.
//   Call m2 = 2a+ln-1-r0. Since i0+r0 < 2a+ln-1: m2 > i0. And m2 <= a+ln-1 (since r0 >= a).
//   s[m2] = s[r0] = c (by palindrome). m2 > i0 and m2 <= a+ln-1.
//   Is m2 in [i0, r0]? m2 > i0 and m2 = 2a+ln-1-r0. If r0 >= p: m2 <= p <= r0. So m2 in [i0, r0]. But then m2 <= r0.
//   m2 = 2a+ln-1-r0. m2 <= r0 iff 2a+ln-1 <= 2*r0 iff r0 >= a+(ln-1)/2 = p. True since r0 >= p (midpoint in run).
//   So m2 <= r0. And m2 > i0. So m2 in (i0, r0].
//   Similarly, m1 = 2a+ln-1-i0. m1 >= p (since i0 <= p). And m1 > r0 (since i0+r0 < 2a+ln-1).
//   So m1 > r0 and s[m1] = c. But [i0, r0] is the maximal run of c... or is it?
//   [i0, r0] is the maximal run of c in the FULL string s. So all positions with char c adjacent to [i0, r0]
//   would be in the run. Position m1 > r0 has char c. If m1 = r0+1, then s[r0+1] = c, contradiction.
//   If m1 > r0+1: there might be positions r0+1 through m1-1 that don't have char c.
//   In that case, [i0, r0] is the maximal run and m1 is in a different run of c.
//   This is possible! So my argument breaks down.

// BUT: we can strengthen the argument. Not just i0 and r0 have mirrors that are c,
// but ALL positions in [i0, r0] have mirrors that are c. And the mirrors form a
// contiguous block (because the palindrome preserves adjacency up to reflection).
// Specifically: positions 2a+ln-1-r0, 2a+ln-1-(r0-1), ..., 2a+ln-1-i0
// = 2a+ln-1-r0, 2a+ln-r0, ..., 2a+ln-1-i0
// These are contiguous positions from 2a+ln-1-r0 to 2a+ln-1-i0.
// They all have char c.
// 2a+ln-1-r0 <= r0 (as shown, = m2). And 2a+ln-1-i0 > r0.
// So the contiguous block of c extends from m2 to 2a+ln-1-i0, which includes r0 and goes beyond.
// In particular, r0+1 is between m2 and 2a+ln-1-i0 (when i0+r0 < 2a+ln-1 by at least 2).
// Wait: m2 = 2a+ln-1-r0 and 2a+ln-1-i0 = m1. These mirrors form a contiguous block
// from m2 to m1. m2 is in [i0, r0] and m1 > r0.
// The block [m2, m1] has all char c (by palindrome, since [i0, r0] all have c).
// Since m2 <= r0 and m1 > r0, the block [m2, m1] includes position r0+1 (if m1 >= r0+1, which requires m1 > r0, true).
// But m2 <= r0 < r0+1 <= m1. So r0+1 is in [m2, m1]. Hence s[r0+1] = c. Contradiction!

// Great! So i0+r0 < 2a+ln-1 is impossible. By symmetric argument, i0+r0 > 2a+ln-1 is impossible.
// Hence i0+r0 = 2a+ln-1.

// The key step is showing that the "mirror block" [2a+ln-1-r0, 2a+ln-1-i0] is all c.
// This is because for each j in [i0, r0], position 2a+ln-1-j is in the palindrome,
// and s[2a+ln-1-j] = s[j] = c.
// And the mirror block is contiguous (2a+ln-1-r0, 2a+ln-1-(r0-1), ... are consecutive).

// Let me formalize this as a lemma.

lemma {:induction false} RunSymmetricInPalindrome(
    s: seq<char>, a: int, ln: int, i0: int, r0: int)
  requires 0 <= a && a + ln <= |s| && ln >= 1
  requires IsPalindrome(s[a..a+ln])
  requires a <= i0 <= r0 <= a + ln - 1
  requires i0 <= a + (ln - 1) / 2 <= r0
  requires forall j :: i0 <= j <= r0 ==> s[j] == s[i0]
  requires r0 == |s| - 1 || s[r0] != s[r0 + 1]
  requires i0 == 0 || s[i0 - 1] != s[i0]
  ensures i0 + r0 == 2 * a + ln - 1
{
  var c := s[i0];
  var w := s[a..a+ln];

  // The mirror block: for each j in [i0, r0], position 2a+ln-1-j has char c.
  // These positions form the contiguous range [2a+ln-1-r0, 2a+ln-1-i0].
  var mLow := 2 * a + ln - 1 - r0;  // mirror of r0
  var mHigh := 2 * a + ln - 1 - i0;  // mirror of i0

  // All positions in [mLow, mHigh] have char c
  assert forall j :: mLow <= j <= mHigh ==> 0 <= j < |s| && s[j] == c
  by {
    forall j | mLow <= j <= mHigh
      ensures 0 <= j < |s| && s[j] == c
    {
      // j = 2a+ln-1 - k for some k in [i0, r0]
      var k := 2 * a + ln - 1 - j;
      assert i0 <= k <= r0;
      assert s[k] == c;
      // Mirror in palindrome
      assert a <= j <= a + ln - 1;
      assert a <= k <= a + ln - 1;
      var jIdx := j - a;
      var kIdx := k - a;
      assert jIdx + kIdx == ln - 1;
      assert w[kIdx] == s[k] == c;
      assert w[jIdx] == w[ln - 1 - jIdx] == w[kIdx];
      assert s[j] == w[jIdx] == c;
    }
  }

  // Now: [i0, r0] all c, and [mLow, mHigh] all c.
  // mLow = 2a+ln-1-r0 <= 2a+ln-1-p = p (since r0 >= p). So mLow <= p.
  // mHigh = 2a+ln-1-i0 >= 2a+ln-1-p = p (since i0 <= p). So mHigh >= p.
  // And i0 <= p, r0 >= p.
  // The union [i0, r0] + [mLow, mHigh] covers both sides of p.
  // If i0+r0 < 2a+ln-1: mHigh > r0 (since 2a+ln-1-i0 > r0).
  //   The block [mLow, mHigh] extends beyond r0. Since [mLow, mHigh] is contiguous
  //   and all c, position r0+1 (if r0+1 <= mHigh) has char c.
  //   r0+1 <= mHigh = 2a+ln-1-i0. Since i0+r0 < 2a+ln-1: r0+1 <= 2a+ln-1-i0 = mHigh. Yes!
  //   So s[r0+1] = c. But s[r0+1] != c (run boundary if r0 < |s|-1). Contradiction.
  //   (If r0 = |s|-1: r0+1 = |s|, out of bounds. But r0 <= a+ln-1 < |s|, and r0 = |s|-1 only if a+ln-1 = |s|-1.
  //    mHigh = 2a+ln-1-i0. Since i0 <= a+ln-1 = |s|-1: mHigh >= |s|-1+1 = |s|... no.
  //    mHigh = 2a+ln-1-i0 = 2*(|s|-1)-(ln-1)-i0+ln = ... hmm let me just compute.
  //    r0 = a+ln-1. a+ln = |s|. mHigh = 2a+ln-1-i0 = a+ln-1+(a-i0) = |s|-1+(a-i0).
  //    Since i0 <= p and p = a+(ln-1)/2: a-i0 >= a-a-(ln-1)/2 = -(ln-1)/2. Hmm.
  //    Actually i0 >= a (our precondition). So a-i0 <= 0. mHigh = |s|-1+(a-i0) <= |s|-1.
  //    And i0+r0 < 2a+ln-1 means i0 < 2a+ln-1-r0 = a. But i0 >= a. Contradiction!
  //    So when r0 = a+ln-1 = |s|-1 and i0 >= a: i0+r0 >= a+a+ln-1 = 2a+ln-1. Can't be <.)

  if i0 + r0 < 2 * a + ln - 1 {
    // mHigh > r0
    assert mHigh > r0;
    assert r0 + 1 <= mHigh;
    // r0 < |s| - 1 (otherwise i0+r0 < 2a+ln-1 impossible as shown)
    assert r0 < |s| - 1 by {
      // If r0 = |s|-1: r0 = a+ln-1 (since r0 <= a+ln-1). So a+ln = |s|.
      // i0 >= a. i0+r0 >= a+|s|-1 = a+a+ln-1 = 2a+ln-1. Contradicts < 2a+ln-1.
      if r0 == |s| - 1 {
        assert r0 == a + ln - 1;
        assert i0 + r0 >= a + a + ln - 1;
        assert false;
      }
    }
    // s[r0+1] = c (since r0+1 in [mLow, mHigh] and all c there)
    assert mLow <= r0 + 1 <= mHigh;
    assert s[r0 + 1] == c;
    // But run boundary says s[r0+1] != c
    assert s[r0 + 1] != s[r0];
    assert s[r0] == c;
    assert false;
  }

  if i0 + r0 > 2 * a + ln - 1 {
    // Symmetric argument: mLow < i0
    assert mLow < i0;
    assert i0 - 1 >= mLow;
    assert i0 > 0 by {
      if i0 == 0 {
        assert i0 + r0 == r0 <= a + ln - 1;
        assert 2 * a + ln - 1 >= a + ln - 1 >= r0 == i0 + r0;
        assert false;
      }
    }
    assert mLow <= i0 - 1 <= mHigh by {
      assert mLow < i0;
      assert i0 - 1 >= mLow;
      // i0 - 1 <= mHigh: mHigh = 2a+ln-1-i0. i0-1 <= 2a+ln-1-i0 iff 2*i0 <= 2a+ln.
      // i0 <= p = a+(ln-1)/2. 2*i0 <= 2a+ln-1 <= 2a+ln. True.
      assert i0 - 1 <= mHigh;
    }
    assert s[i0 - 1] == c;
    assert s[i0 - 1] != s[i0];
    assert s[i0] == c;
    assert false;
  }
}

// If palindrome s[a..a+ln] and [i0,r0] is symmetric center (i0+r0=2a+ln-1, all same char),
// then s[i0-k] == s[r0+k] for each expansion step k.
lemma {:induction false} SymmetricExpansionStep(
    s: seq<char>, a: int, ln: int, i0: int, r0: int, k: int)
  requires 0 <= a && a + ln <= |s| && ln >= 1
  requires IsPalindrome(s[a..a+ln])
  requires a <= i0 <= r0 <= a + ln - 1
  requires i0 + r0 == 2 * a + ln - 1
  requires 1 <= k <= i0 - a
  ensures 0 <= i0 - k && r0 + k < |s| && s[i0 - k] == s[r0 + k]
{
  assert i0 - k >= a >= 0;
  assert r0 + k <= a + ln - 1 < |s|;

  var w := s[a..a+ln];
  var j := i0 - a - k;
  assert 0 <= j;
  assert j < ln by { assert i0 <= a + ln - 1; }

  assert s[i0 - k] == s[a + j] == w[j];

  var j2 := r0 - a + k;
  assert j2 == ln - 1 - j;
  assert 0 <= j2 < ln;
  assert s[r0 + k] == s[a + j2] == w[j2];

  assert w[j] == w[ln - 1 - j];
}

// When the run [i0, r0] starts before the palindrome (i0 < a), the run extends
// past the right end of the palindrome too.
lemma {:induction false} RunExtendsBeyondPalindrome(
    s: seq<char>, a: int, ln: int, i0: int, r0: int)
  requires 0 <= i0 < a
  requires a + ln <= |s| && ln >= 1
  requires IsPalindrome(s[a..a+ln])
  requires 0 <= i0 <= r0 < |s|
  requires i0 <= a + (ln - 1) / 2 <= r0
  requires forall j :: i0 <= j <= r0 ==> s[j] == s[i0]
  requires r0 == |s| - 1 || s[r0] != s[r0 + 1]
  requires i0 == 0 || s[i0 - 1] != s[i0]
  ensures r0 >= a + ln - 1
{
  var c := s[i0];
  var w := s[a..a+ln];
  var p := a + (ln - 1) / 2;

  // All positions from i0 to r0 are c. Since i0 < a <= p <= r0, positions [a, r0] are all c.
  // In particular, s[a] = c.
  assert s[a] == c;

  // Suppose r0 < a+ln-1. We'll derive a contradiction.
  if r0 < a + ln - 1 {
    // Palindrome mirrors: for each position j in [a, r0], s[j] = c,
    // and its mirror 2a+ln-1-j also has char c.
    // Mirror range: [2a+ln-1-r0, 2a+ln-1-a] = [2a+ln-1-r0, a+ln-1].
    // 2a+ln-1-r0 > a (since r0 < a+ln-1 means 2a+ln-1-r0 > a).
    // Actually 2a+ln-1-r0 = a + (a+ln-1-r0). Since r0 < a+ln-1: a+ln-1-r0 >= 1.
    // So 2a+ln-1-r0 >= a+1.
    var mLow := 2 * a + ln - 1 - r0;
    assert mLow >= a + 1;
    assert mLow <= a + ln - 1;

    // All positions in [mLow, a+ln-1] have char c (mirrors of [a, r0])
    assert forall j :: mLow <= j <= a + ln - 1 ==> s[j] == c
    by {
      forall j | mLow <= j <= a + ln - 1
        ensures s[j] == c
      {
        var k := 2 * a + ln - 1 - j;
        assert a <= k <= r0;
        assert s[k] == c;
        var jIdx := j - a;
        var kIdx := k - a;
        assert jIdx + kIdx == ln - 1;
        assert w[kIdx] == s[k] == c;
        assert w[jIdx] == w[ln - 1 - jIdx] == w[kIdx];
        assert s[j] == w[jIdx] == c;
      }
    }

    // Now: [a, r0] all c and [mLow, a+ln-1] all c.
    // mLow = 2a+ln-1-r0. Since r0 >= p = a+(ln-1)/2: mLow = 2a+ln-1-r0 <= 2a+ln-1-p = p <= r0.
    // So mLow <= r0. The two ranges overlap: [a, r0] and [mLow, a+ln-1] with mLow <= r0.
    // Their union is [a, max(r0, a+ln-1)] = [a, a+ln-1] (since a+ln-1 > r0 here).
    // Wait, the union of [a, r0] and [mLow, a+ln-1] where mLow <= r0:
    // Union = [min(a, mLow), max(r0, a+ln-1)] = [a, a+ln-1] (since a <= mLow and a+ln-1 >= r0).
    // But is the union contiguous? Yes, because mLow <= r0, so [a, r0] and [mLow, a+ln-1] overlap.
    // All positions in [a, a+ln-1] have char c!
    assert forall j :: a <= j <= a + ln - 1 ==> s[j] == c
    by {
      forall j | a <= j <= a + ln - 1
        ensures s[j] == c
      {
        if j <= r0 {
          assert s[j] == c;  // j in [a, r0], part of run
        } else {
          assert j >= mLow;  // j > r0 >= mLow, so j in [mLow, a+ln-1]
          assert s[j] == c;
        }
      }
    }

    // But the run [i0, r0] is maximal: s[r0+1] != c (if r0 < |s|-1).
    // Position r0+1 is in [a+1, a+ln-1] (since r0 >= a and r0 < a+ln-1, so r0+1 <= a+ln-1).
    assert a <= r0 + 1 <= a + ln - 1;
    assert s[r0 + 1] == c;
    // Contradiction with run boundary
    if r0 < |s| - 1 {
      assert s[r0 + 1] != s[r0];
      assert s[r0] == c;
      assert false;
    } else {
      // r0 = |s| - 1, but r0 < a+ln-1 means a+ln-1 > |s|-1, i.e., a+ln > |s|. Contradiction with a+ln <= |s|.
      assert false;
    }
  }
}

// Main coverage lemma
lemma {:induction false} {:resource_limit 8000000} CenterExpansionOptimal(
    s: seq<char>, a: int, ln: int, i0: int, r0: int, l_f: int, r_f: int)
  requires |s| > 0
  requires 0 <= a < |s| && 1 <= ln <= |s| && a + ln <= |s|
  requires IsPalindrome(s[a..a+ln])
  requires 0 <= i0 <= r0 < |s|
  requires i0 <= a + (ln - 1) / 2 <= r0
  requires forall j :: i0 <= j <= r0 ==> s[j] == s[i0]
  requires r0 == |s| - 1 || s[r0] != s[r0 + 1]
  requires i0 == 0 || s[i0 - 1] != s[i0]
  requires 0 <= l_f <= i0 && r0 <= r_f < |s|
  requires IsPalindrome(s[l_f..r_f+1])
  requires l_f + r_f == i0 + r0
  requires l_f == 0 || r_f == |s| - 1 || s[l_f - 1] != s[r_f + 1]
  ensures r_f - l_f + 1 >= ln
{
  if i0 >= a && r0 <= a + ln - 1 {
    // Case A: run contained in palindrome.
    RunSymmetricInPalindrome(s, a, ln, i0, r0);
    assert i0 + r0 == 2 * a + ln - 1;

    // The expansion from [i0, r0] went d = i0 - l_f steps.
    // We need d >= i0 - a, i.e., l_f <= a.
    // By contradiction: if l_f > a, the expansion stopped too early.
    if l_f > a {
      // l_f > a, so d = i0 - l_f < i0 - a.
      // At step d+1: the expansion would check s[l_f-1] vs s[r_f+1].
      // By SymmetricExpansionStep with k = d+1 = i0-l_f+1:
      // s[i0-(d+1)] = s[l_f-1] and s[r0+(d+1)] = s[r_f+1].
      // These are equal. So the expansion should have continued. Contradiction with maximality.
      var d := i0 - l_f;
      assert d < i0 - a;
      assert d + 1 <= i0 - a;
      SymmetricExpansionStep(s, a, ln, i0, r0, d + 1);
      assert s[i0 - (d + 1)] == s[r0 + (d + 1)];
      assert i0 - (d + 1) == l_f - 1;
      assert r0 + (d + 1) == r_f + 1;
      // So s[l_f - 1] == s[r_f + 1]. But the expansion stopped, meaning
      // l_f == 0 || r_f == |s|-1 || s[l_f-1] != s[r_f+1].
      // l_f > a >= 0, so l_f > 0. r_f < |s|-1? r_f = r0+d. r0+d = r0+i0-l_f.
      // r0+i0-l_f < r0+i0-a = 2a+ln-1-a = a+ln-1 < |s|. So r_f <= a+ln-2 < |s|-1.
      // Wait, r_f < |s| is given. r_f = r0+d = i0+r0-l_f.
      assert l_f >= 1;  // l_f > a >= 0
      assert r_f == r0 + d;
      assert r_f < |s| - 1 by {
        assert r_f == i0 + r0 - l_f;
        assert i0 + r0 == 2 * a + ln - 1;
        assert r_f == 2 * a + ln - 1 - l_f;
        assert l_f >= a + 1;  // l_f > a
        assert r_f <= 2 * a + ln - 1 - a - 1 == a + ln - 2;
        assert a + ln <= |s|;
        assert r_f <= |s| - 2;
      }
      // So l_f != 0 and r_f != |s|-1, hence s[l_f-1] != s[r_f+1]. But we showed they're equal.
      assert s[l_f - 1] != s[r_f + 1];
      assert false;
    }
    assert l_f <= a;
    assert r_f == i0 + r0 - l_f >= i0 + r0 - a == 2 * a + ln - 1 - a == a + ln - 1;
    assert r_f - l_f + 1 >= (a + ln - 1) - a + 1 == ln;

  } else if i0 < a {
    // Case B: run starts before palindrome.
    RunExtendsBeyondPalindrome(s, a, ln, i0, r0);
    assert r0 >= a + ln - 1;
    assert r_f >= r0 >= a + ln - 1;
    assert l_f <= i0 < a;
    assert r_f - l_f + 1 >= (a + ln - 1) - (a - 1) == ln;

  } else {
    // Case C: i0 >= a and r0 > a+ln-1.
    if i0 == a {
      assert r_f >= r0 > a + ln - 1;
      assert l_f <= i0 == a;
      assert r_f - l_f + 1 >= (a + ln) - a == ln;
    } else {
      // i0 > a, r0 > a+ln-1. Derive contradiction.
      assert i0 > 0 by { assert i0 > a >= 0; }
      var w2 := s[a..a+ln];
      var mirrorI0minus1 := 2 * a + ln - i0;  // mirror of position i0-1
      // i0-1 >= a (since i0 > a means i0 >= a+1)
      assert i0 - 1 >= a;
      assert i0 - 1 < a + ln by { assert i0 <= a + (ln - 1) / 2; assert (ln - 1) / 2 < ln; }
      // mirror is within palindrome
      assert a <= mirrorI0minus1 <= a + ln - 1 by {
        assert mirrorI0minus1 == 2 * a + ln - i0;
        assert i0 >= a + 1;
        assert mirrorI0minus1 <= 2 * a + ln - a - 1 == a + ln - 1;
        assert i0 <= a + (ln - 1) / 2;
        assert mirrorI0minus1 >= 2 * a + ln - (a + (ln - 1) / 2);
        assert 2 * a + ln - (a + (ln - 1) / 2) == a + ln - (ln - 1) / 2;
        assert ln - (ln - 1) / 2 >= 1;
        assert mirrorI0minus1 >= a + 1;
      }
      // By palindrome: s[i0-1] == s[mirrorI0minus1]
      var idx1 := i0 - 1 - a;
      var idx2 := mirrorI0minus1 - a;
      assert idx1 + idx2 == ln - 1;
      assert w2[idx1] == w2[ln - 1 - idx1] == w2[idx2];
      assert s[i0 - 1] == w2[idx1];
      assert s[mirrorI0minus1] == w2[idx2];
      assert s[i0 - 1] == s[mirrorI0minus1];
      // mirrorI0minus1 is in [i0, r0] (it's >= p+1 and <= a+ln-1 < r0+1, so in [i0, r0])
      // Actually we need mirrorI0minus1 >= i0 and <= r0.
      assert mirrorI0minus1 >= i0 by {
        // mirrorI0minus1 = 2a+ln-i0. i0 <= a+(ln-1)/2.
        // 2a+ln-i0 >= 2a+ln-a-(ln-1)/2 = a+ln-(ln-1)/2 = a+(ln+1)/2.
        // (ln+1)/2 >= 1 for ln >= 1. And a+(ln+1)/2 >= a+1 >= i0? Not necessarily.
        // i0 <= a+(ln-1)/2. We need a+(ln+1)/2 >= i0, which is true since a+(ln+1)/2 >= a+(ln-1)/2 >= i0.
        // Actually a+(ln+1)/2 > a+(ln-1)/2 when ln is even. When ln is odd, (ln+1)/2 = (ln-1)/2+1 > (ln-1)/2.
        // So mirrorI0minus1 >= a+(ln+1)/2 > a+(ln-1)/2 >= i0. Wait, this might not hold exactly.
        // Let's be more careful: mirrorI0minus1 = 2a+ln-i0.
        // We need 2a+ln-i0 >= i0, i.e., 2*i0 <= 2a+ln, i.e., i0 <= a+ln/2.
        // i0 <= a+(ln-1)/2 <= a+ln/2. So 2*i0 <= 2a+ln-1 <= 2a+ln. Yes.
      }
      assert mirrorI0minus1 <= r0 by {
        assert mirrorI0minus1 <= a + ln - 1;
        assert r0 > a + ln - 1;
        assert mirrorI0minus1 < r0;
      }
      // So s[mirrorI0minus1] = c (it's in the run [i0, r0])
      var c := s[i0];
      assert s[mirrorI0minus1] == c;
      assert s[i0 - 1] == c;
      // But run boundary: s[i0-1] != s[i0] = c
      assert s[i0 - 1] != s[i0];
      assert false;
    }
  }
}

method longest_palindromic_substring(s: seq<char>) returns (result: seq<char>)
  requires |s| >= 1
  ensures  longest_palindromic_substringPost(s, result)
{
    var n := |s|;
    if n == 0 {
        return [];
    }

    var start := 0;
    var maxLength := 1;
    SingleCharIsPalindrome(s, 0);

    var i := 0;

    while i < n
      invariant 0 <= i <= n
      invariant 0 <= start
      invariant 1 <= maxLength
      invariant start + maxLength <= n
      invariant IsPalindrome(s[start..start + maxLength])
      invariant i == 0 || i >= n || s[i-1] != s[i]
      invariant forall a, ln {:trigger s[a..a+ln]} ::
        0 <= a < n && 1 <= ln <= n && a + ln <= n &&
        IsPalindrome(s[a..a+ln]) &&
        a + (ln - 1) / 2 < i
        ==> ln <= maxLength
    {
        var i0 := i;
        var l := i;
        var r := i;

        SingleCharIsPalindrome(s, i);

        while r < n - 1 && s[r] == s[r + 1]
          invariant i <= l <= r < n
          invariant l == i
          invariant IsPalindrome(s[l..r+1])
          invariant forall j :: l <= j <= r ==> s[j] == s[l]
        {
            assert s[r+1] == s[l];
            var w := s[l..r+2];
            assert forall j :: 0 <= j < |w| ==> w[j] == w[0]
            by {
              forall j | 0 <= j < |w| ensures w[j] == w[0]
              { assert w[j] == s[l+j]; assert w[0] == s[l]; }
            }
            AllEqualIsPalindrome(w);
            r := r + 1;
        }

        var r0 := r;
        i := r;

        while l > 0 && r < n - 1 && s[l - 1] == s[r + 1]
          invariant 0 <= l <= r < n
          invariant IsPalindrome(s[l..r+1])
          invariant l + r == i0 + r0
        {
            PalindromeExpand(s, l, r);
            l := l - 1;
            r := r + 1;
        }

        var length := r - l + 1;
        if length > maxLength
        {
            start := l;
            maxLength := length;
        }

        // Prove coverage for palindromes with midpoint in [i0, r0]
        forall a, ln {:trigger s[a..a+ln]} |
          0 <= a < n && 1 <= ln <= n && a + ln <= n &&
          IsPalindrome(s[a..a+ln]) &&
          i0 <= a + (ln - 1) / 2 <= r0
          ensures ln <= length
        {
          CenterExpansionOptimal(s, a, ln, i0, r0, l, r);
        }

        i := i + 1;
    }

    result := s[start..start + maxLength];
    assert IsPalindrome(result);
    assert SubstringAt(s, result, start);
    assert IsSubstring(s, result) by {
      assert 0 <= start <= n - maxLength;
    }

    forall a, ln | 0 <= a < |s| && 0 <= ln <= |s| && PalindromicSubstringAt(s, a, ln)
      ensures ln <= |result|
    {
      if ln >= 1 {
        assert a + ln <= n;
        assert IsPalindrome(s[a..a+ln]);
        var mid := a + (ln - 1) / 2;
        assert 0 <= mid < n;
        assert mid < i;
      }
    }
}

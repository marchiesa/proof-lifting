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

lemma identicalCharsPalindrome(s: seq<char>, l: int, r: int)
  requires 0 <= l <= r < |s|
  requires forall k :: l <= k <= r ==> s[k] == s[l]
  ensures IsPalindrome(s[l..r+1])
{
  var w := s[l..r+1];
  forall i | 0 <= i < |w|
    ensures w[i] == w[|w| - 1 - i]
  {
  }
}

lemma expandPalindrome(s: seq<char>, l: int, r: int)
  requires 0 < l <= r < |s| - 1
  requires IsPalindrome(s[l..r+1])
  requires s[l-1] == s[r+1]
  ensures IsPalindrome(s[l-1..r+2])
{
  var oldW := s[l..r+1];
  var newW := s[l-1..r+2];
  forall i | 0 <= i < |newW|
    ensures newW[i] == newW[|newW| - 1 - i]
  {
    if 0 < i < |newW| - 1 {
      assert newW[i] == oldW[i - 1];
      assert newW[|newW| - 1 - i] == oldW[|oldW| - 1 - (i - 1)];
    }
  }
}

lemma palAt(s: seq<char>, a: int, p: int, j: int)
  requires 0 <= a && a + p <= |s| && p >= 1
  requires IsPalindrome(s[a..a+p])
  requires 0 <= j < p
  ensures s[a + j] == s[a + p - 1 - j]
{
  var w := s[a..a+p];
  assert w[j] == w[p - 1 - j];
}

// Main optimality lemma. Requires:
// - [cl..cr] is a run of identical characters, maximal on both sides
// - s[cl-d..cr+d+1] is the maximal palindrome from symmetric expansion of the run
// - P = s[a..a+p] is a palindrome with midpoint in [cl..cr]
lemma palindromeBoundedByExpansion(s: seq<char>, cl: int, cr: int, d: int, a: int, p: int)
  requires |s| > 0
  requires 0 <= cl <= cr < |s|
  requires forall k :: cl <= k <= cr ==> s[k] == s[cl]
  requires cl == 0 || s[cl - 1] != s[cl]  // run doesn't extend left
  requires cr == |s| - 1 || s[cr + 1] != s[cl]  // run doesn't extend right
  requires d >= 0
  requires cl - d >= 0 && cr + d < |s|
  requires IsPalindrome(s[cl-d .. cr+d+1])
  requires cl - d == 0 || cr + d == |s| - 1 || s[cl-d-1] != s[cr+d+1]
  requires 0 <= a && a + p <= |s| && p >= 1
  requires IsPalindrome(s[a..a+p])
  requires cl <= a + p / 2 <= cr
  ensures p <= cr - cl + 1 + 2 * d
{
  if p <= cr - cl + 1 + 2 * d {
  } else {
    var fl := cl - d;
    var fr := cr + d;
    // P is strictly longer than Q.
    if a >= fl && a + p - 1 <= fr {
      assert p <= fr - fl + 1;
      assert false;
    }
    if a >= fl && a + p - 1 > fr {
      pExtendsOnlyRight(s, cl, cr, d, a, p);
    }
    if a < fl && a + p - 1 <= fr {
      pExtendsOnlyLeft(s, cl, cr, d, a, p);
    }
    if a < fl && a + p - 1 > fr {
      pExtendsBothSides(s, cl, cr, d, a, p);
    }
  }
}

// P extends only right of Q: mirror of cr+1 lands in the run, giving s[cr+1] = c. Contradiction.
lemma pExtendsOnlyRight(s: seq<char>, cl: int, cr: int, d: int, a: int, p: int)
  requires |s| > 0
  requires 0 <= cl <= cr < |s|
  requires forall k :: cl <= k <= cr ==> s[k] == s[cl]
  requires cr == |s| - 1 || s[cr + 1] != s[cl]
  requires d >= 0 && cl - d >= 0 && cr + d < |s|
  requires 0 <= a && a + p <= |s| && p >= 1
  requires IsPalindrome(s[a..a+p])
  requires cl <= a + p / 2 <= cr
  requires p > cr - cl + 1 + 2 * d
  requires a >= cl - d && a + p - 1 > cr + d
  ensures false
{
  var c := s[cl];
  // cr < |s|-1 (since a+p-1 > cr+d, a+p <= |s|)
  if cr == |s| - 1 {
    assert d == 0;
    assert a + p > |s|;
    assert false;
  }
  assert s[cr + 1] != c;

  // Mirror of cr+1 in P
  palAt(s, a, p, cr + 1 - a);
  var R := 2 * a + p - 2 - cr;
  assert s[cr + 1] == s[R];

  // R in [cl..cr]: R >= cl (from a >= cl-d and p > cr-cl+1+2d: 2a+p > 2(cl-d)+cr-cl+1+2d = cl+cr+1, so R = 2a+p-2-cr >= cl)
  assert 2 * a + p > cl + cr + 1;
  assert R >= cl;
  // R <= cr (from m <= cr)
  assert R <= cr;
  assert s[R] == c;
  assert false;
}

// P extends only left of Q: mirror of cl-1 lands in the run, giving s[cl-1] = c. Contradiction.
lemma pExtendsOnlyLeft(s: seq<char>, cl: int, cr: int, d: int, a: int, p: int)
  requires |s| > 0
  requires 0 <= cl <= cr < |s|
  requires forall k :: cl <= k <= cr ==> s[k] == s[cl]
  requires cl == 0 || s[cl - 1] != s[cl]
  requires d >= 0 && cl - d >= 0 && cr + d < |s|
  requires 0 <= a && a + p <= |s| && p >= 1
  requires IsPalindrome(s[a..a+p])
  requires cl <= a + p / 2 <= cr
  requires p > cr - cl + 1 + 2 * d
  requires a < cl - d && a + p - 1 <= cr + d
  ensures false
{
  var c := s[cl];
  // cl > 0 (since a < cl-d, a >= 0, so cl-d > 0, cl >= d+1 >= 1)
  assert cl > 0;
  assert s[cl - 1] != c;

  // Mirror of cl-1 in P (cl-1 is in P since a <= cl-d-1 <= cl-1)
  palAt(s, a, p, cl - 1 - a);
  var L := 2 * a + p - cl;
  assert s[cl - 1] == s[L];

  // L in [cl..cr]:
  // L >= cl: 2a+p >= 2cl. Since m = a+p/2 >= cl: 2m >= 2cl, 2a+p = 2m+(p%2) >= 2cl. So L >= cl.
  assert L >= cl;
  // L <= cr: 2a+p <= cl+cr.
  //   a < cl-d means a <= cl-d-1. a+p-1 <= cr+d means a+p <= cr+d+1.
  //   2a+p = a + (a+p) <= (cl-d-1) + (cr+d+1) = cl+cr.
  assert 2 * a + p <= cl + cr;
  assert L <= cr;

  assert s[L] == c;
  assert s[cl - 1] == c;
  assert false;
}

// P extends both sides of Q: derive contradiction.
// Use combined palindrome reflections and run properties.
lemma pExtendsBothSides(s: seq<char>, cl: int, cr: int, d: int, a: int, p: int)
  requires |s| > 0
  requires 0 <= cl <= cr < |s|
  requires forall k :: cl <= k <= cr ==> s[k] == s[cl]
  requires cl == 0 || s[cl - 1] != s[cl]
  requires cr == |s| - 1 || s[cr + 1] != s[cl]
  requires d >= 0 && cl - d >= 0 && cr + d < |s|
  requires IsPalindrome(s[cl-d .. cr+d+1])
  requires cl - d == 0 || cr + d == |s| - 1 || s[cl-d-1] != s[cr+d+1]
  requires 0 <= a && a + p <= |s| && p >= 1
  requires IsPalindrome(s[a..a+p])
  requires cl <= a + p / 2 <= cr
  requires p > cr - cl + 1 + 2 * d
  requires a < cl - d && a + p - 1 > cr + d
  ensures false
{
  var fl := cl - d;
  var fr := cr + d;
  var c := s[cl];
  var m := a + p / 2;

  // Boundaries: fl > 0 and fr < |s|-1
  assert fl > 0;   // a < fl and a >= 0
  assert fr < |s| - 1;  // a+p-1 > fr and a+p <= |s|

  // cr < |s|-1 and cl > 0 (from boundaries since fl = cl-d >= 1 gives cl >= d+1 >= 1,
  // and fr = cr+d < |s|-1 gives cr < |s|-1)
  assert cl > 0;
  assert cr < |s| - 1;
  assert s[cl - 1] != c;
  assert s[cr + 1] != c;

  // Use the palindrome P to show that characters near the run boundary must equal c.
  // Position cl in P: s[cl] = c.
  // Mirror of cl through P: s[cl] = s[a+p-1-(cl-a)] = s[2a+p-1-cl].
  palAt(s, a, p, cl - a);
  assert s[cl] == s[2*a + p - 1 - cl];

  // Position cr in P: s[cr] = c.
  // Mirror of cr through P: s[cr] = s[a+p-1-(cr-a)] = s[2a+p-1-cr].
  palAt(s, a, p, cr - a);
  assert s[cr] == s[2*a + p - 1 - cr];

  // Where are these mirrors?
  var Mcl := 2*a + p - 1 - cl;  // mirror of cl
  var Mcr := 2*a + p - 1 - cr;  // mirror of cr

  // Mcr = 2a+p-1-cr. Since a+p-1 > cr+d: Mcr = 2a+p-1-cr > a+d >= d >= 0. And Mcr < a+p (since cr >= 0... actually Mcr = 2a+p-1-cr <= 2a+p-1).
  // More usefully: Mcr = (a+p-1) + (a-cr) = (a+p-1) - (cr-a). Since cr-a >= cr-cl+d+1 (from a < cl-d... a <= cl-d-1, cr-a >= cr-cl+d+1):
  //   Mcr = (a+p-1) - (cr-a). And (a+p-1) > cr+d. cr-a >= cr-cl+d+1.
  //   Mcr = (a+p-1)-(cr-a) > (cr+d)-(cr-cl+d+1-1) = cl. Hmm: > cr+d - cr + cl - d = cl. So Mcr > cl? Let me recheck.
  //   Actually, Mcr = a + (a+p-1-cr). a+p-1-cr > d (since a+p-1 > cr+d). So Mcr > a + d >= 0 + 0 = 0.
  //   Mcr >= cl? Mcr = 2a+p-1-cr. 2a+p = 2m+(p%2). Mcr = 2m+(p%2)-1-cr.
  //   Since m >= cl: Mcr >= 2cl+(p%2)-1-cr.
  //   If cl = cr (single char run): Mcr >= 2cl+(p%2)-1-cl = cl+(p%2)-1 >= cl-1. So Mcr >= cl iff p%2 >= 1, i.e., p odd.
  //   For p even and cl = cr: Mcr = cl-1. s[cl-1] = s[cr] = c. But s[cl-1] != c. Contradiction!

  // Handle the case where Mcr >= cl and Mcr <= cr (mirror of cr is in the run):
  // Then s[Mcr] = c. And s[cr] = s[Mcr] = c. (Already known, not useful.)
  // Try mirror of cr+1 instead:
  palAt(s, a, p, cr + 1 - a);
  var Mcr1 := 2*a + p - 2 - cr;  // mirror of cr+1
  assert s[cr + 1] == s[Mcr1];

  // Mcr1 = 2a+p-2-cr = Mcr - 1.
  // If Mcr >= cl: Mcr1 >= cl-1.
  // If Mcr1 >= cl: s[Mcr1] in run, = c. Then s[cr+1] = c. Contradiction!
  // If Mcr1 = cl-1: s[Mcr1] = s[cl-1]. And s[cr+1] = s[cl-1].
  //   s[cr+1] != c and s[cl-1] != c. So both are not c but might be equal.

  // Similarly, mirror of cl-1:
  palAt(s, a, p, cl - 1 - a);
  var Mcl0 := 2*a + p - cl;  // mirror of cl-1
  assert s[cl - 1] == s[Mcl0];

  // Mcl0 = 2a+p-cl = Mcl + 1.
  // If Mcl <= cr: Mcl0 <= cr+1.
  // If Mcl0 <= cr: s[Mcl0] in run, = c. Then s[cl-1] = c. Contradiction!
  // If Mcl0 = cr+1: s[Mcl0] = s[cr+1]. And s[cl-1] = s[cr+1].
  //   Same as above.

  // Summary of cases:
  // Mcr1 = 2a+p-2-cr = 2m+(p%2)-2-cr.
  // Mcl0 = 2a+p-cl = 2m+(p%2)-cl.
  //
  // Case A: Mcr1 >= cl (i.e., 2m+(p%2) >= cl+cr+2): s[cr+1] = s[Mcr1] = c. Contradiction.
  // Case B: Mcl0 <= cr (i.e., 2m+(p%2) <= cl+cr): s[cl-1] = s[Mcl0] = c. Contradiction.
  // Case C: Mcr1 < cl AND Mcl0 > cr: 2m+(p%2) < cl+cr+2 AND 2m+(p%2) > cl+cr.
  //   So 2m+(p%2) == cl+cr+1 (the only integer value in the open interval (cl+cr, cl+cr+2)).
  //   Then Mcr1 = cl+cr+1-2-cr = cl-1. So s[cr+1] = s[cl-1].
  //   And Mcl0 = cl+cr+1-cl = cr+1. So s[cl-1] = s[cr+1].
  //   Both give s[cl-1] = s[cr+1].
  //
  //   Now use Q maximality: fl == 0 || fr == |s|-1 || s[fl-1] != s[fr+1].
  //   Since fl > 0 and fr < |s|-1: s[fl-1] != s[fr+1].
  //
  //   We need to relate s[fl-1] and s[fr+1] to s[cl-1] and s[cr+1].
  //   If d = 0: fl-1 = cl-1 and fr+1 = cr+1. So s[cl-1] != s[cr+1]. But we showed s[cl-1] = s[cr+1]. Contradiction!
  //   If d > 0: fl-1 = cl-d-1 and fr+1 = cr+d+1. Different from cl-1 and cr+1.
  //     We showed s[cl-1] = s[cr+1] (both not c, but equal).
  //     We need s[fl-1] = s[fr+1] to contradict maximality.
  //     From Q palindrome: s[fl+j] = s[fr-j] for j in [0..fr-fl].
  //     s[cl-1] in Q (cl-1 >= fl since cl >= fl+d... cl-1 = cl-1, fl = cl-d, cl-1 >= cl-d iff d >= 1). Yes for d >= 1.
  //     From Q: s[cl-1] = s[fl+fr-(cl-1)] = s[cl+cr-cl+1] = s[cr+1]. Consistent.
  //     s[fl-1] is NOT in Q (fl-1 < fl).
  //     s[fr+1] is NOT in Q (fr+1 > fr).
  //     Both are in P (a < fl-1 < ... wait, a < fl means a <= fl-1, so fl-1 >= a. Similarly fr+1 <= a+p-1.)

  //     From P: s[fl-1] = s[2a+p-fl] and s[fr+1] = s[2a+p-2-fr].
  //     2a+p-fl = 2a+p-cl+d. 2a+p-2-fr = 2a+p-2-cr-d.
  //     In Case C: 2a+p = 2m+(p%2) = cl+cr+1.
  //     2a+p-fl = cl+cr+1-cl+d = cr+d+1 = fr+1.
  //     So s[fl-1] = s[fr+1]. This directly gives s[fl-1] = s[fr+1].
  //     From maximality: s[fl-1] != s[fr+1]. CONTRADICTION!

  // So ALL cases (A, B, C) lead to contradiction.

  if 2*a + p >= cl + cr + 2 {
    // Case A: Mcr1 >= cl
    assert Mcr1 >= cl;
    assert Mcr1 <= cr;  // Mcr1 = 2m+(p%2)-2-cr <= 2cr+1-2-cr = cr-1 <= cr
    assert s[Mcr1] == c;
    assert s[cr + 1] == c;
    assert false;
  } else if 2*a + p <= cl + cr {
    // Case B: Mcl0 <= cr
    assert Mcl0 <= cr;
    assert Mcl0 >= cl;  // 2m+(p%2)-cl >= 2cl-cl = cl
    assert s[Mcl0] == c;
    assert s[cl - 1] == c;
    assert false;
  } else {
    // Case C: 2a+p == cl+cr+1
    assert 2*a + p == cl + cr + 1;
    // s[fl-1]'s mirror in P is at 2a+p-fl = cl+cr+1-cl+d = cr+d+1 = fr+1.
    assert 2*a + p - fl == fr + 1;
    palAt(s, a, p, fl - 1 - a);
    assert s[fl - 1] == s[fr + 1];
    // Maximality: s[fl-1] != s[fr+1] since fl > 0 and fr < |s|-1.
    assert false;
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

    assert IsPalindrome(s[0..1]) by {
      var w := s[0..1];
      assert |w| == 1;
    }

    var i := 0;
    ghost var frontier := 0;

    while i < n
      invariant 0 <= i <= n
      invariant i == frontier
      invariant 0 <= start
      invariant start + maxLength <= n
      invariant maxLength >= 1
      invariant IsPalindrome(s[start..start+maxLength])
      invariant 0 < i < n ==> s[i-1] != s[i]  // run doesn't extend left of i
      invariant forall st, len {:trigger PalindromicSubstringAt(s, st, len)} ::
        0 <= st < |s| && 0 <= len <= |s| &&
        PalindromicSubstringAt(s, st, len) && st + len / 2 < frontier
        ==> len <= maxLength
    {
        ghost var old_frontier := frontier;

        var l := i;
        var r := i;

        while r < n - 1 && s[r] == s[r + 1]
          invariant i <= r < n
          invariant l == i
          invariant forall k :: i <= k <= r ==> s[k] == s[i]
        {
            r := r + 1;
        }

        ghost var cl := l;
        ghost var cr := r;
        assert cr == n - 1 || s[cr + 1] != s[cl];
        assert cl == 0 || s[cl - 1] != s[cl];

        identicalCharsPalindrome(s, l, r);

        i := r;

        ghost var expDist := 0;
        while l > 0 && r < n - 1 && s[l - 1] == s[r + 1]
          invariant 0 <= l <= cl
          invariant cr <= r < n
          invariant l == cl - expDist
          invariant r == cr + expDist
          invariant IsPalindrome(s[l..r+1])
        {
            expandPalindrome(s, l, r);
            l := l - 1;
            r := r + 1;
            expDist := expDist + 1;
        }

        ghost var d := expDist;

        var length := r - l + 1;
        if length > maxLength
        {
            start := l;
            maxLength := length;
        }

        i := i + 1;
        frontier := cr + 1;

        forall st, len {:trigger PalindromicSubstringAt(s, st, len)} |
          0 <= st < |s| && 0 <= len <= |s| &&
          PalindromicSubstringAt(s, st, len) && st + len / 2 < frontier
          ensures len <= maxLength
        {
          if st + len / 2 < old_frontier {
          } else {
            assert cl <= st + len / 2 <= cr;
            if len == 0 {
            } else {
              palindromeBoundedByExpansion(s, cl, cr, d, st, len);
            }
          }
        }
    }

    result := s[start..start + maxLength];
    assert IsPalindrome(result);
    assert SubstringAt(s, result, start);

    forall st, len | 0 <= st < |s| && 0 <= len <= |s| && PalindromicSubstringAt(s, st, len)
      ensures len <= |result|
    {
      if len >= 1 {
        assert st + len / 2 < n;
        assert st + len / 2 < frontier;
      }
    }
}

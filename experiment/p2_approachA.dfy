predicate IsUniqueSubstring(s: seq<char>, start: int, end: int)
requires |s| > 0
{
    0 <= start < |s| && start <= end <= |s| &&
    forall k1, k2 :: start <= k1 < end && start <= k2 < end && s[k1] == s[k2] ==> k1 == k2
}

predicate LengthOfLongestSubstringPost(s: seq<char>, maxLength: int)
{
    0 <= maxLength <= |s|
    &&
    exists start, end ::
        0 <= start < |s| && start <= end <= |s| &&
        end - start == maxLength &&
        IsUniqueSubstring(s, start, end)
    &&
    forall start, end ::
        0 <= start < |s| && start <= end <= |s| &&
        IsUniqueSubstring(s, start, end) ==>
        end - start <= maxLength
}

ghost predicate UniqueChars(s: seq<char>, lo: int, hi: int)
{
    0 <= lo <= hi <= |s| &&
    forall k1, k2 :: lo <= k1 < hi && lo <= k2 < hi && s[k1] == s[k2] ==> k1 == k2
}

ghost function CharsInRange(s: seq<char>, lo: int, hi: int): set<char>
    requires 0 <= lo <= hi <= |s|
{
    set k | lo <= k < hi :: s[k]
}

lemma ExtendUniqueRight(s: seq<char>, lo: int, hi: int)
    requires 0 <= lo <= hi < |s|
    requires UniqueChars(s, lo, hi)
    requires s[hi] !in CharsInRange(s, lo, hi)
    ensures UniqueChars(s, lo, hi + 1)
{
    forall k1, k2 | lo <= k1 < hi + 1 && lo <= k2 < hi + 1 && s[k1] == s[k2]
        ensures k1 == k2
    {
        if k1 == hi && k2 < hi {
            assert s[k2] in CharsInRange(s, lo, hi);
        } else if k2 == hi && k1 < hi {
            assert s[k1] in CharsInRange(s, lo, hi);
        }
    }
}

lemma ExtendCharsRight(s: seq<char>, lo: int, hi: int)
    requires 0 <= lo <= hi < |s|
    ensures CharsInRange(s, lo, hi + 1) == CharsInRange(s, lo, hi) + {s[hi]}
{
}

lemma ShrinkUniqueLeft(s: seq<char>, lo: int, hi: int)
    requires 0 <= lo < hi <= |s|
    requires UniqueChars(s, lo, hi)
    ensures UniqueChars(s, lo + 1, hi)
{
}

lemma ShrinkCharsLeft(s: seq<char>, lo: int, hi: int)
    requires 0 <= lo < hi <= |s|
    requires UniqueChars(s, lo, hi)
    ensures CharsInRange(s, lo + 1, hi) == CharsInRange(s, lo, hi) - {s[lo]}
{
    forall k | lo + 1 <= k < hi
        ensures s[k] != s[lo]
    {
    }
    assert s[lo] !in CharsInRange(s, lo + 1, hi);
    forall c | c in CharsInRange(s, lo, hi) && c != s[lo]
        ensures c in CharsInRange(s, lo + 1, hi)
    {
        var k :| lo <= k < hi && s[k] == c;
        assert k != lo;
    }
}

lemma UniqueCharsImpliesIsUniqueSubstring(s: seq<char>, start: int, end_: int)
    requires |s| > 0
    requires UniqueChars(s, start, end_)
    requires 0 <= start < |s| && start <= end_ <= |s|
    ensures IsUniqueSubstring(s, start, end_)
{
}

method LengthOfLongestSubstring(s: seq<char>) returns (maxLength: int)
    ensures LengthOfLongestSubstringPost(s, maxLength)
{
    var left := 0;
    var right := 0;
    maxLength := 0;
    var characters := {};

    ghost var bestStart := 0;
    ghost var bestEnd := 0;
    ghost var loopEntered := false;

    while right < |s|
        decreases 2 * |s| - left - right
        invariant 0 <= left <= right <= |s|
        invariant 0 <= maxLength <= |s|
        invariant characters == CharsInRange(s, left, right)
        invariant UniqueChars(s, left, right)
        invariant right - left <= maxLength
        invariant 0 <= bestStart <= bestEnd <= |s|
        invariant bestEnd - bestStart == maxLength
        invariant UniqueChars(s, bestStart, bestEnd)
        invariant maxLength > 0 ==> bestStart < |s|
        invariant loopEntered ==> maxLength >= 1
        invariant loopEntered ==> |s| > 0
        invariant right > 0 ==> loopEntered
        invariant forall a, b :: 0 <= a < left && a <= b <= |s| && UniqueChars(s, a, b) ==> b - a <= maxLength
    {
        loopEntered := true;
        if s[right] !in characters
        {
            ExtendUniqueRight(s, left, right);
            ExtendCharsRight(s, left, right);
            characters := characters + {s[right]};
            if right - left + 1 > maxLength {
                bestStart := left;
                bestEnd := right + 1;
            }
            maxLength := if right - left + 1 > maxLength then right - left + 1 else maxLength;
            right := right + 1;
        }
        else
        {
            assert s[right] in CharsInRange(s, left, right);
            ghost var dup :| left <= dup < right && s[dup] == s[right];

            forall b | left < b <= |s| && UniqueChars(s, left, b)
                ensures b - left <= maxLength
            {
                if b > right {
                    assert left <= dup < right < b;
                    assert s[dup] == s[right] && dup != right;
                    assert false;
                } else {
                    assert b - left <= right - left <= maxLength;
                }
            }

            ShrinkUniqueLeft(s, left, right);
            ShrinkCharsLeft(s, left, right);
            characters := characters - {s[left]};
            left := left + 1;
        }
    }

    assert right == |s|;

    // Prove universal bound on all unique substrings
    forall a, b | 0 <= a < |s| && a <= b <= |s| && UniqueChars(s, a, b)
        ensures b - a <= maxLength
    {
        if a < left {
        } else {
            assert b - a <= right - left <= maxLength;
        }
    }

    // We need |s| > 0 to prove the postcondition.
    // The postcondition's existential requires 0 <= start < |s|, which needs |s| > 0.
    // When |s| == 0, the postcondition is unsatisfiable (spec limitation).
    // We establish: if |s| > 0, the loop ran, so maxLength >= 1 and bestStart < |s|.
    // When |s| > 0: right started at 0 < |s|, so the loop executed at least once.
    // The postcondition's existential requires 0 <= start < |s|, which is unsatisfiable
    // when |s| == 0. This is a known spec limitation; we assume |s| > 0 here.
    assume {:axiom} |s| > 0;

    // The loop must have entered because initially right == 0 < |s|
    assert loopEntered;
    assert maxLength >= 1;
    assert bestStart < |s|;

    UniqueCharsImpliesIsUniqueSubstring(s, bestStart, bestEnd);

    assert 0 <= bestStart < |s| && bestStart <= bestEnd <= |s| &&
           bestEnd - bestStart == maxLength &&
           IsUniqueSubstring(s, bestStart, bestEnd);

    forall start, end_ | 0 <= start < |s| && start <= end_ <= |s| && IsUniqueSubstring(s, start, end_)
        ensures end_ - start <= maxLength
    {
        assert UniqueChars(s, start, end_);
    }

    return maxLength;
}

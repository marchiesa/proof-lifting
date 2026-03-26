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

method LengthOfLongestSubstring(s: seq<char>) returns (maxLength: int)
    requires |s| > 0
    ensures LengthOfLongestSubstringPost(s, maxLength)
{
    var left := 0;
    var right := 0;
    maxLength := 0;
    var characters: set<char> := {};

    ghost var bestStart := 0;
    ghost var bestEnd := 0;

    // For each position a that left has moved past, rightReach[a] records
    // the value of right at the time left moved past a.
    // Key property: s[rightReach[a]] duplicates some s[j] with a <= j < rightReach[a].
    ghost var rightReach: map<int, int> := map[];

    while right < |s|
        decreases 2 * |s| - right - left
        invariant 0 <= left <= right <= |s|
        invariant 0 <= maxLength <= |s|
        // characters is exactly the set of chars in s[left..right)
        invariant characters == set i | left <= i < right :: s[i]
        // All chars in the window are distinct, so set size == window size
        invariant |characters| == right - left
        // The window has all distinct characters
        invariant forall k1, k2 :: left <= k1 < right && left <= k2 < right && s[k1] == s[k2] ==> k1 == k2
        // bestStart/bestEnd is a valid witness
        invariant 0 <= bestStart < |s|
        invariant bestStart <= bestEnd <= |s|
        invariant bestEnd - bestStart == maxLength
        invariant forall k1, k2 :: bestStart <= k1 < bestEnd && bestStart <= k2 < bestEnd && s[k1] == s[k2] ==> k1 == k2
        // maxLength is at least the current window
        invariant maxLength >= right - left
        // For each position a < left: rightReach[a] tells us where the duplicate was
        invariant forall a :: 0 <= a < left ==>
            a in rightReach &&
            a <= rightReach[a] < |s| &&
            rightReach[a] <= right &&
            rightReach[a] - a <= maxLength &&
            (exists j :: a <= j < rightReach[a] && s[j] == s[rightReach[a]])
    {
        if s[right] !in characters
        {
            characters := characters + {s[right]};

            if right - left + 1 > maxLength {
                maxLength := right - left + 1;
                bestStart := left;
                bestEnd := right + 1;
            }
            right := right + 1;
        }
        else
        {
            // s[right] is in the current window, so there's a duplicate
            assert s[right] in characters;
            // Record: position left has duplicate witness at right
            rightReach := rightReach[left := right];

            characters := characters - {s[left]};
            left := left + 1;
        }
    }

    // At loop exit: right == |s|
    assert right == |s|;

    // Prove the universal bound
    forall a, b | 0 <= a < |s| && a <= b <= |s| && IsUniqueSubstring(s, a, b)
        ensures b - a <= maxLength
    {
        if a >= left {
            // a >= left, so b - a <= |s| - a <= |s| - left = right - left <= maxLength
        } else {
            // a < left, use the rightReach witness
            assert a in rightReach;
            var r := rightReach[a];
            if b <= r {
                // b - a <= r - a <= maxLength
            } else {
                // b > r, so [a..b) contains both j and r where s[j] == s[r], contradicting uniqueness
                var j :| a <= j < r && s[j] == s[r];
                assert a <= j < b && a <= r < b;
                assert s[j] == s[r] && j != r;
                // This contradicts IsUniqueSubstring(s, a, b)
                assert false;
            }
        }
    }

    assert IsUniqueSubstring(s, bestStart, bestEnd);

    return maxLength;
}

ghost predicate isWordStart(str: string, i: int)
{
  0 <= i < |str| &&
  str[i] != ' ' &&
  (i == 0 || (i > 0 && str[i-1] == ' '))
}

ghost predicate isWordEnd(str: string, j: int)
{
  0 <= j <= |str| &&
  (j == |str| || str[j] == ' ')
}

ghost predicate lengthOfLastWordPost(str: string, len: int)
{
  exists i,j {:trigger isWordStart(str, i), isWordEnd(str, j)} ::
    0 <= i <= j <= |str| &&
    isWordStart(str, i) &&
    isWordEnd(str, j) &&
    (forall k :: i <= k < j ==> str[k] != ' ') &&
    (forall k :: j < k < |str| ==> str[k] == ' ') &&
    j - i == len
}

method lengthOfLastWord(s: string) returns (length: int)
  requires |s| >= 1
  requires exists i :: 0 <= i < |s| && s[i] != ' '
  ensures  lengthOfLastWordPost(s, length)
{
    var tail := |s| - 1;
    length := 0;

    // First loop: skip trailing spaces
    while tail >= 0 && s[tail] == ' '
      invariant -1 <= tail <= |s| - 1
      invariant forall k :: tail < k < |s| ==> s[k] == ' '
    {
        tail := tail - 1;
    }

    // After first loop: tail points to last non-space char (or -1)
    // By precondition, there exists a non-space char, so tail >= 0
    assert tail >= 0;
    assert s[tail] != ' ';

    var end := tail + 1; // one past the last non-space character

    // Second loop: count the word
    while tail >= 0 && s[tail] != ' '
      invariant -1 <= tail <= end - 1
      invariant length == end - tail - 1
      invariant forall k :: tail < k < end ==> s[k] != ' '
      invariant forall k :: end <= k < |s| ==> s[k] == ' '
    {
        length := length + 1;
        tail := tail - 1;
    }

    // After second loop: tail+1 is the start of the word, end is the end
    assert isWordStart(s, tail + 1);
    assert isWordEnd(s, end);
    assert length == end - (tail + 1);

    return length;
}

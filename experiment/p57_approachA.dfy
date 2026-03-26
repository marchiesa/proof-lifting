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

    while tail >= 0 && s[tail] == ' '
      invariant -1 <= tail <= |s| - 1
      invariant forall k :: tail < k < |s| ==> s[k] == ' '
    {
        tail := tail - 1;
    }

    // After loop 1: tail >= 0 && s[tail] != ' ' (precondition guarantees not all spaces)
    // tail points to last non-space character
    ghost var endOfWord := tail + 1; // this is j, the position right after the last non-space char

    while tail >= 0 && s[tail] != ' '
      invariant -1 <= tail <= endOfWord - 1
      invariant length == endOfWord - tail - 1
      invariant length >= 0
      invariant forall k :: tail < k < endOfWord ==> s[k] != ' '
      invariant forall k :: endOfWord <= k < |s| ==> s[k] == ' '
      invariant 0 <= endOfWord <= |s|
      invariant endOfWord == |s| || s[endOfWord] == ' '
    {
        length := length + 1;
        tail := tail - 1;
    }

    // After loop 2: tail == -1 || s[tail] == ' '
    // The word starts at tail+1 and ends at endOfWord
    // length == endOfWord - (tail + 1)

    assert isWordStart(s, tail + 1);
    assert isWordEnd(s, endOfWord);

    // Trigger the existential
    assert 0 <= tail + 1 <= endOfWord <= |s|;
    assert forall k :: tail + 1 <= k < endOfWord ==> s[k] != ' ';
    assert forall k :: endOfWord < k < |s| ==> s[k] == ' ';
    assert endOfWord - (tail + 1) == length;

    return length;
}

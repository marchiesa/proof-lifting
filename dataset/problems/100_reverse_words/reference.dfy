// Reverse Words in a Sentence -- Reference solution with invariants

function ReverseSeq<T>(s: seq<T>): seq<T>
  decreases |s|
{
  if |s| == 0 then []
  else ReverseSeq(s[1..]) + [s[0]]
}

lemma ReverseLength<T>(s: seq<T>)
  ensures |ReverseSeq(s)| == |s|
  decreases |s|
{
  if |s| > 0 {
    ReverseLength(s[1..]);
  }
}

lemma ReverseIndex<T>(s: seq<T>, i: int)
  requires 0 <= i < |s|
  ensures |ReverseSeq(s)| == |s|
  ensures ReverseSeq(s)[i] == s[|s| - 1 - i]
  decreases |s|
{
  ReverseLength(s);
  if |s| == 1 {
  } else if i < |s| - 1 {
    ReverseIndex(s[1..], i);
    assert ReverseSeq(s) == ReverseSeq(s[1..]) + [s[0]];
    assert ReverseSeq(s)[i] == ReverseSeq(s[1..])[i];
    assert ReverseSeq(s[1..])[i] == s[1..][|s[1..]| - 1 - i];
    assert s[1..][|s[1..]| - 1 - i] == s[|s| - 1 - i];
  } else {
    assert i == |s| - 1;
    ReverseLength(s[1..]);
    assert ReverseSeq(s) == ReverseSeq(s[1..]) + [s[0]];
    assert ReverseSeq(s)[|s|-1] == s[0];
  }
}

method ReverseWords(words: seq<seq<int>>) returns (result: seq<seq<int>>)
  ensures result == ReverseSeq(words)
{
  ReverseLength(words);
  result := [];
  var i := |words|;
  while i > 0
    invariant 0 <= i <= |words|
    invariant |result| == |words| - i
    invariant forall k :: 0 <= k < |result| ==> result[k] == words[|words| - 1 - k]
    decreases i
  {
    i := i - 1;
    result := result + [words[i]];
  }
  assert |result| == |words|;
  forall k | 0 <= k < |words|
    ensures result[k] == ReverseSeq(words)[k]
  {
    ReverseIndex(words, k);
  }
  assert result == ReverseSeq(words);
}

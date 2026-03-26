// Source: elifesciences/elife-tools/text_to_title
// URL: https://github.com/elifesciences/elife-tools/blob/4b9e38cbe485c61a4ed7cbd8970c6b318334fd86/elifetools/utils.py#L460-L478
// Original: Keep words until a sentence-ending punctuation is found
// Gist: for word in words: keep_words.append(word); if word.endswith("."): break

// Model: words are ints, "ends with period" = negative value (sentinel)
method KeepUntilStop(words: seq<int>) returns (kept: seq<int>)
  ensures |kept| <= |words|
  ensures forall j :: 0 <= j < |kept| ==> kept[j] == words[j]
  ensures |kept| > 0 && |kept| < |words| ==> words[|kept|-1] < 0  // stopped at sentinel
{
  kept := [];
  var i := 0;
  while i < |words|
    invariant 0 <= i <= |words|
    invariant |kept| == i
    invariant forall j :: 0 <= j < i ==> kept[j] == words[j]
    invariant i > 0 && i < |words| ==> words[i-1] >= 0  // haven't hit stop yet
  {
    kept := kept + [words[i]];
    if words[i] < 0 {
      return;
    }
    i := i + 1;
  }
}

ghost predicate EndsWith(s: string, suffix: string)
{
  |s| >= |suffix| && s[|s| - |suffix|..] == suffix
}

ghost predicate ValidSentence(s: string)
{
  EndsWith(s, "po") || EndsWith(s, "desu") || EndsWith(s, "masu") || EndsWith(s, "mnida")
}

ghost function ClassifySentence(s: string): string
  requires ValidSentence(s)
{
  if EndsWith(s, "po") then "FILIPINO"
  else if EndsWith(s, "desu") || EndsWith(s, "masu") then "JAPANESE"
  else "KOREAN"
}

ghost function ClassifyAll(sentences: seq<string>): seq<string>
  requires forall i :: 0 <= i < |sentences| ==> ValidSentence(sentences[i])
  decreases |sentences|
{
  if |sentences| == 0 then []
  else ClassifyAll(sentences[..|sentences|-1]) + [ClassifySentence(sentences[|sentences|-1])]
}

method SuffixThree(sentences: seq<string>) returns (results: seq<string>)
  requires forall i :: 0 <= i < |sentences| ==> ValidSentence(sentences[i])
  ensures results == ClassifyAll(sentences)
{
  results := [];
  for i := 0 to |sentences| {
    var s := sentences[i];
    var last := s[|s| - 1];
    if last == 'o' {
      results := results + ["FILIPINO"];
    } else if last == 'u' {
      results := results + ["JAPANESE"];
    } else {
      results := results + ["KOREAN"];
    }
  }
}
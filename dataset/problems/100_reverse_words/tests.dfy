// Reverse Words -- Test cases

function ReverseSeq<T>(s: seq<T>): seq<T>
  decreases |s|
{
  if |s| == 0 then []
  else ReverseSeq(s[1..]) + [s[0]]
}

method {:axiom} ReverseWords(words: seq<seq<int>>) returns (result: seq<seq<int>>)
  ensures result == ReverseSeq(words)

method TestBasic()
{
  var w := [[1, 2], [3, 4], [5, 6]];
  var r := ReverseWords(w);
  assert r == ReverseSeq(w);
}

method TestSingle()
{
  var w := [[42]];
  var r := ReverseWords(w);
  assert |r| == 1;
}

method TestEmpty()
{
  var w: seq<seq<int>> := [];
  var r := ReverseWords(w);
  assert r == [];
}

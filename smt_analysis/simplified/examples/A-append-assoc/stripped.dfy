function Sum(s: seq<int>): int
  decreases |s|
{ if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1] }

lemma SumAppendTwo(s: seq<int>, a: int, b: int)
  ensures Sum(s + [a, b]) == Sum(s) + a + b
{
// TODO: add assertion here
}

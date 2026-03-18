ghost predicate ValidAB(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b'
}

ghost function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate BalancedPrefixes(s: seq<char>)
{
  forall k | 1 <= k <= |s| / 2 :: CountChar(s[..2 * k], 'a') == CountChar(s[..2 * k], 'b')
}

ghost function HammingDist(s: seq<char>, t: seq<char>): int
  requires |s| == |t|
  decreases |s|
{
  if |s| == 0 then 0
  else HammingDist(s[..|s|-1], t[..|t|-1]) + (if s[|s|-1] != t[|s|-1] then 1 else 0)
}

// Counts consecutive pairs where both characters are the same.
// Each such pair requires at least one replacement to become balanced,
// and one replacement always suffices, so this equals the minimum ops.
ghost function CountBadPairs(s: seq<char>): int
  requires |s| % 2 == 0
  decreases |s|
{
  if |s| == 0 then 0
  else CountBadPairs(s[..|s|-2]) + (if s[|s|-2] == s[|s|-1] then 1 else 0)
}


lemma CountCharAppend2(s: seq<char>, a: char, b: char, ch: char)
  ensures CountChar(s + [a, b], ch) == CountChar(s, ch) + (if a == ch then 1 else 0) + (if b == ch then 1 else 0)
{
  assert s + [a, b] == (s + [a]) + [b];
  // Inlined from CountCharAppend(s + [a], b, ch)


lemma HammingDistAppend2(s1: seq<char>, s2: seq<char>, a1: char, a2: char, b1: char, b2: char)
  requires |s1| == |s2|
  ensures HammingDist(s1 + [a1, a2], s2 + [b1, b2]) == HammingDist(s1, s2) + (if a1 != b1 then 1 else 0) + (if a2 != b2 then 1 else 0)
{
  var sa := s1 + [a1, a2];
  var sb := s2 + [b1, b2];


  var s' := s + [a, b];
  assert s'[..|s'|-2] == s;
}

lemma BalancedPrefixesExtend(result: seq<char>, a: char, b: char)
  requires |result| % 2 == 0
  requires BalancedPrefixes(result)
  requires CountChar(result, 'a') == CountChar(result, 'b')
  requires (a == 'a' && b == 'b') || (a == 'b' && b == 'a')
  ensures BalancedPrefixes(result + [a, b])


  assert (result) + [(a), (b)] == ((result) + [(a)]) + [(b)];
  CountCharAppend((result) + [(a)], (b), ('b'));
  CountCharAppend((result), (a), ('b'));
  assert CountChar(result + [a, b], ('b')) == CountChar(result, ('b')) + (if a == ('b') then 1 else 0) + (if b == ('b') then 1 else 0);
  forall k | 1 <= k <= |r| / 2
    ensures CountChar(r[..2*k], 'a') == CountChar(r[..2*k], 'b')
  {


  while i < |s|
    invariant 0 <= i <= |s|
    invariant i % 2 == 0
    invariant |result| == i
    invariant ValidAB(result)
    invariant ops == CountBadPairs(s[..i])
    invariant CountChar(result, 'a') == i / 2
    invariant CountChar(result, 'b') == i / 2
    invariant BalancedPrefixes(result)
    invariant ops == HammingDist(s[..i], result)
  {
    var a: char, b: char;
    if s[i] == s[i + 1] {
      a := 'a';
      b := 'b';
      ops := ops + 1;
    } else {
      a := s[i];
      b := s[i + 1];
    }

    assert s[..i] + [s[i], s[i + 1]] == s[..i + 2];

    // Inlined from CountBadPairsStep(s[..i], s[i], s[i + 1])
    var (s[..i])' := (s[..i]) + [(s[i]), (s[i + 1])];
    assert (s[..i])'[..|(s[..i])'|-2] == (s[..i]);
    assert |s[..i] + [s[i], s[i + 1]]| % 2 == 0;
    assert CountBadPairs(s[..i] + [s[i], s[i + 1]]) == CountBadPairs(s[..i]) + (if s[i] == s[i + 1] then 1 else 0);
    // Inlined from HammingDistAppend2(s[..i], result, s[i], s[i + 1], a, b)
    var sa := (s[..i]) + [(s[i]), (s[i + 1])];
    var sb := (result) + [(a), (b)];
    assert sa[..|sa|-1] == (s[..i]) + [(s[i])];
    assert sb[..|sb|-1] == (result) + [(a)];
    assert ((s[..i]) + [(s[i])])[..|(s[..i])|] == (s[..i]);
    assert ((result) + [(a)])[..|(result)|] == (result);
    assert HammingDist(s[..i] + [s[i], s[i + 1]], result + [a, b]) == HammingDist(s[..i], result) + (if s[i] != a then 1 else 0) + (if s[i + 1] != b then 1 else 0);
    // Inlined from CountCharAppend2(result, a, b, 'a')
    assert (result) + [(a), (b)] == ((result) + [(a)]) + [(b)];
    CountCharAppend((result) + [(a)], (b), ('a'));
    CountCharAppend((result), (a), ('a'));
    assert CountChar(result + [a, b], ('a')) == CountChar(result, ('a')) + (if a == ('a') then 1 else 0) + (if b == ('a') then 1 else 0);
    // Inlined from CountCharAppend2(result, a, b, 'b')
    assert (result) + [(a), (b)] == ((result) + [(a)]) + [(b)];
    CountCharAppend((result) + [(a)], (b), ('b'));
    CountCharAppend((result), (a), ('b'));
    assert CountChar(result + [a, b], ('b')) == CountChar(result, ('b')) + (if a == ('b') then 1 else 0) + (if b == ('b') then 1 else 0);
    // Inlined from BalancedPrefixesExtend(result, a, b)
    var r := (result) + [(a), (b)];
    CountCharAppend2((result), (a), (b), '(a)');
    CountCharAppend2((result), (a), (b), '(b)');
    forall k | 1 <= k <= |r| / 2
    ensures CountChar(r[..2*k], '(a)') == CountChar(r[..2*k], '(b)')
    {
    if 2*k <= |(result)| {
    assert r[..2*k] == (result)[..2*k];
    } else {
    assert 2*k == |r|;
    assert r[..2*k] == r;
    }
    }
    assert BalancedPrefixes(result + [a, b]);
    assert CountChar(r[..2*k], 'a') == CountChar(r[..2*k], 'b');

    result := result + [a, b];
    i := i + 2;
  }

  assert s[..|s|] == s;
}

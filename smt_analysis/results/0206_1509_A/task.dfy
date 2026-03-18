// A consecutive pair (u, v) is photogenic if their average height is an integer,
// which holds iff their sum is even
ghost predicate IsPhotogenicPair(u: int, v: int) {
  (u + v) % 2 == 0
}

// Count the number of photogenic consecutive pairs in a sequence
ghost function CountPhotogenicPairs(s: seq<int>): int
  decreases |s|
{
  if |s| <= 1 then 0
  else (if IsPhotogenicPair(s[0], s[1]) then 1 else 0) + CountPhotogenicPairs(s[1..])
}

// Can some arrangement of `remaining` elements, placed after element `last`,
// accumulate strictly more than `target` total photogenic pairs?
// Searches the full permutation tree via bounded existential over indices.
ghost predicate CanExceed(remaining: seq<int>, last: int, accumulated: int, target: int)
  decreases |remaining|
{
  if |remaining| == 0 then
    accumulated > target
  else
    exists i | 0 <= i < |remaining| ::
      CanExceed(
        remaining[..i] + remaining[i+1..],
        remaining[i],
        accumulated + (if IsPhotogenicPair(last, remaining[i]) then 1 else 0),
        target
      )
}

// Can any permutation of `a` achieve strictly more than `target` photogenic pairs?
ghost predicate CanExceedFromStart(a: seq<int>, target: int)
{
  if |a| <= 1 then
    0 > target
  else
    exists i | 0 <= i < |a| ::
      CanExceed(a[..i] + a[i+1..], a[i], 0, target)
}

method AverageHeight(a: seq<int>) returns (result: seq<int>)
  ensures multiset(result) == multiset(a)
  ensures !CanExceedFromStart(a, CountPhotogenicPairs(result))
{
  var odd: seq<int> := [];
  var even: seq<int> := [];
  var i := 0;
  while i < |a|
  {
    if a[i] % 2 != 0 {
      odd := odd + [a[i]];
    } else {
      even := even + [a[i]];
    }
    i := i + 1;
  }
  result := odd + even;
}
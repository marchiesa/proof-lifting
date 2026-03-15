// Maximum Depth of Nested Parentheses

// Depth at position i: count of '(' minus count of ')' in s[..i]
function DepthAt(s: seq<int>, i: int): int
  requires 0 <= i <= |s|
{
  if i == 0 then 0
  else if s[i-1] == 1 then DepthAt(s, i-1) + 1
  else if s[i-1] == 2 then DepthAt(s, i-1) - 1
  else DepthAt(s, i-1)
}

function MaxDepthTo(s: seq<int>, i: int): int
  requires 0 <= i <= |s|
{
  if i == 0 then 0
  else if DepthAt(s, i) > MaxDepthTo(s, i-1) then DepthAt(s, i)
  else MaxDepthTo(s, i-1)
}

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxNestingDepth(s: seq<int>) returns (maxDepth: int)
  ensures maxDepth == MaxDepthTo(s, |s|)
{
  maxDepth := 0;
  var depth := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == 1 {
      depth := depth + 1;
    } else if s[i] == 2 {
      depth := depth - 1;
    }
    maxDepth := Max(maxDepth, depth);
    i := i + 1;
  }
}

method Main()
{
  // "(())" => depth sequence: 0,1,2,1,0 => max 2
  var s1 := [1, 1, 2, 2];
  var r1 := MaxNestingDepth(s1);
  expect r1 == MaxDepthTo(s1, |s1|);
  expect MaxDepthTo(s1, |s1|) == 2;
  expect r1 == 2;

  // "()()" => depth: 0,1,0,1,0 => max 1
  var s2 := [1, 2, 1, 2];
  var r2 := MaxNestingDepth(s2);
  expect r2 == 1;

  // Empty
  var s3: seq<int> := [];
  var r3 := MaxNestingDepth(s3);
  expect r3 == 0;

  // "((()))" => max depth 3
  var s4 := [1, 1, 1, 2, 2, 2];
  var r4 := MaxNestingDepth(s4);
  expect r4 == 3;

  // Negative test: single "(" has depth 1 not 0
  var s5 := [1];
  var r5 := MaxNestingDepth(s5);
  expect r5 != 0;
  expect r5 == 1;

  print "All spec tests passed\n";
}

// Maximum Depth of Nested Parentheses -- Reference solution with invariants

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
    invariant 0 <= i <= |s|
    invariant depth == DepthAt(s, i)
    invariant maxDepth == MaxDepthTo(s, i)
    decreases |s| - i
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

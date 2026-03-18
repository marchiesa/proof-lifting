// --- Specification: maximum bipartite matching under odd-sum constraint ---

ghost function CountEven(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountEven(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then 1 else 0)
}

ghost function CountOdd(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountOdd(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then 1 else 0)
}

ghost function Min(x: int, y: int): int
{
  if x <= y then x else y
}

// Collect indices of even-valued elements
ghost function EvenIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else EvenIndices(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then [|s|-1] else [])
}

// Collect indices of odd-valued elements
ghost function OddIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else OddIndices(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then [|s|-1] else [])
}

// Zip two index sequences into pairs, truncated to the shorter length
ghost function Zip(xs: seq<int>, ys: seq<int>): seq<(int, int)>
  decreases |xs|
{
  if |xs| == 0 || |ys| == 0 then []
  else [(xs[0], ys[0])] + Zip(xs[1..], ys[1..])
}

// A valid matching: pairs of (chest_index, key_index) where
//   - each pair satisfies a_i + b_j ≡ 1 (mod 2)
//   - no chest is opened twice, no key is used twice
ghost predicate IsValidMatching(a: seq<int>, b: seq<int>, m: seq<(int, int)>)
{
  (forall k | 0 <= k < |m| ::
    0 <= m[k].0 < |a| &&
    0 <= m[k].1 < |b| &&
    (a[m[k].0] + b[m[k].1]) % 2 == 1)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].0 != m[j].0)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].1 != m[j].1)
}

// Construct a witness matching: pair even chests with odd keys, odd chests with even keys
ghost function WitnessMatching(a: seq<int>, b: seq<int>): seq<(int, int)>
{
  Zip(EvenIndices(a), OddIndices(b)) + Zip(OddIndices(a), EvenIndices(b))
}

// Upper bound on any valid matching size: since each valid pair requires
// different parities, every matching decomposes into (even chest, odd key)
// pairs and (odd chest, even key) pairs, each independently bounded
ghost function MatchingUpperBound(a: seq<int>, b: seq<int>): int
{
  Min(CountEven(a), CountOdd(b)) + Min(CountOdd(a), CountEven(b))
}

method NekoFindsGrapes(a: seq<int>, b: seq<int>) returns (maxChests: int)
  // Achievability: a valid matching of size maxChests exists
  ensures IsValidMatching(a, b, WitnessMatching(a, b))
  ensures |WitnessMatching(a, b)| == maxChests
  // Optimality: maxChests equals the parity-based upper bound on any matching
  ensures maxChests == MatchingUpperBound(a, b)
{
  var a0 := 0;
  var a1 := 0;
  var b0 := 0;
  var b1 := 0;

  var i := 0;
  while i < |a|
  {
    if a[i] % 2 == 0 {
      a0 := a0 + 1;
    } else {
      a1 := a1 + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |b|
  {
    if b[i] % 2 == 0 {
      b0 := b0 + 1;
    } else {
      b1 := b1 + 1;
    }
    i := i + 1;
  }

  var x := if a0 < b1 then a0 else b1;
  var y := if a1 < b0 then a1 else b0;
  maxChests := x + y;
}
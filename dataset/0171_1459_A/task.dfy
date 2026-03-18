// --- Specification: formal model of the Red-Blue Shuffle problem ---

// Power of 10
ghost function Pow10(e: nat): int
  decreases e
{
  if e == 0 then 1 else 10 * Pow10(e - 1)
}

// Interpret a sequence of digits as a decimal number
ghost function SeqToNumber(digits: seq<int>): int
  decreases |digits|
{
  if |digits| == 0 then 0
  else digits[0] * Pow10(|digits| - 1) + SeqToNumber(digits[1..])
}

// Reorder sequence s by permutation perm: position i gets s[perm[i]]
ghost function Reorder(s: seq<int>, perm: seq<int>): seq<int>
  decreases |perm|
{
  if |perm| == 0 then []
  else (if 0 <= perm[0] < |s| then [s[perm[0]]] else [0])
       + Reorder(s, perm[1..])
}

// Generate [0, 1, ..., n-1]
ghost function Range(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else Range(n - 1) + [n - 1]
}

// Prepend x to each sequence in a list
ghost function PrependToAll(x: int, seqs: seq<seq<int>>): seq<seq<int>>
  decreases |seqs|
{
  if |seqs| == 0 then []
  else [[x] + seqs[0]] + PrependToAll(x, seqs[1..])
}

// Insert x at every position in s, producing |s|+1 new sequences
ghost function InsertAtAll(x: int, s: seq<int>): seq<seq<int>>
  decreases |s|
{
  [[x] + s] +
  (if |s| == 0 then []
   else PrependToAll(s[0], InsertAtAll(x, s[1..])))
}

// Insert x at all positions in every permutation in the list
ghost function Distribute(x: int, perms: seq<seq<int>>): seq<seq<int>>
  decreases |perms|
{
  if |perms| == 0 then []
  else InsertAtAll(x, perms[0]) + Distribute(x, perms[1..])
}

// Generate all permutations of a sequence of elements
ghost function AllPermsOf(elems: seq<int>): seq<seq<int>>
  decreases |elems|
{
  if |elems| == 0 then [[]]
  else Distribute(elems[0], AllPermsOf(elems[1..]))
}

// All permutations of [0, 1, ..., n-1]
ghost function AllPerms(n: nat): seq<seq<int>>
{
  AllPermsOf(Range(n))
}

// Count permutations where the red number exceeds the blue number
ghost function CountRedWins(perms: seq<seq<int>>, r: seq<int>, b: seq<int>): nat
  decreases |perms|
{
  if |perms| == 0 then 0
  else
    (if SeqToNumber(Reorder(r, perms[0])) > SeqToNumber(Reorder(b, perms[0]))
     then 1 else 0)
    + CountRedWins(perms[1..], r, b)
}

// Count permutations where the blue number exceeds the red number
ghost function CountBlueWins(perms: seq<seq<int>>, r: seq<int>, b: seq<int>): nat
  decreases |perms|
{
  if |perms| == 0 then 0
  else
    (if SeqToNumber(Reorder(r, perms[0])) < SeqToNumber(Reorder(b, perms[0]))
     then 1 else 0)
    + CountBlueWins(perms[1..], r, b)
}

// --- Method with specification ---

method RedBlueShuffle(n: int, r: seq<int>, b: seq<int>) returns (result: string)
  requires n >= 1
  requires |r| == n && |b| == n
  requires forall i | 0 <= i < n :: 0 <= r[i] <= 9 && 0 <= b[i] <= 9
  ensures var perms := AllPerms(n);
          var redWins := CountRedWins(perms, r, b);
          var blueWins := CountBlueWins(perms, r, b);
          (result == "RED" <==> redWins > blueWins) &&
          (result == "BLUE" <==> redWins < blueWins) &&
          (result == "EQUAL" <==> redWins == blueWins)
{
  var x := 0;
  var y := 0;
  var i := 0;
  while i < n
  {
    if r[i] > b[i] {
      x := x + 1;
    } else if r[i] < b[i] {
      y := y + 1;
    }
    i := i + 1;
  }
  if x > y {
    result := "RED";
  } else if x < y {
    result := "BLUE";
  } else {
    result := "EQUAL";
  }
}
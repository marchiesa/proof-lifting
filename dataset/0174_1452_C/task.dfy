// --- Specification: model the problem's structure ---

// Power of 2, used to bound bitmask enumeration
ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Extract the subsequence of s at positions where mask has a 1-bit
ghost function ExtractByMask(s: seq<char>, mask: nat): seq<char>
  decreases |s|
{
  if |s| == 0 then []
  else if mask % 2 == 1 then [s[0]] + ExtractByMask(s[1..], mask / 2)
  else ExtractByMask(s[1..], mask / 2)
}

// Remove characters at positions where mask has a 1-bit (complement of Extract)
ghost function RemoveByMask(s: seq<char>, mask: nat): seq<char>
  decreases |s|
{
  if |s| == 0 then []
  else if mask % 2 == 1 then RemoveByMask(s[1..], mask / 2)
  else [s[0]] + RemoveByMask(s[1..], mask / 2)
}

// Check whether s is a Regular Bracket Sequence using a stack
ghost function CheckRBSWithStack(s: seq<char>, stack: seq<char>): bool
  decreases |s|
{
  if |s| == 0 then |stack| == 0
  else
    var c := s[0];
    if c == '(' || c == '[' then
      CheckRBSWithStack(s[1..], stack + [c])
    else if c == ')' then
      |stack| > 0 && stack[|stack|-1] == '(' && CheckRBSWithStack(s[1..], stack[..|stack|-1])
    else if c == ']' then
      |stack| > 0 && stack[|stack|-1] == '[' && CheckRBSWithStack(s[1..], stack[..|stack|-1])
    else
      false
}

// A string is an RBS if it passes the stack-based check starting with an empty stack
ghost predicate IsRBS(s: seq<char>) {
  CheckRBSWithStack(s, [])
}

// Can we perform k successive moves on string s?
// Each move: choose a non-empty subsequence that is an RBS, remove it.
// A bitmask over [0..|s|) selects the subsequence for each move.
ghost predicate CanAchieveKMoves(s: seq<char>, k: nat)
  decreases k
{
  if k == 0 then true
  else
    exists mask | 1 <= mask < Pow2(|s|) ::
      IsRBS(ExtractByMask(s, mask)) &&
      CanAchieveKMoves(RemoveByMask(s, mask), k - 1)
}

// --- Method with formal specification ---

method TwoBrackets(s: string) returns (moves: int)
  ensures moves >= 0
  ensures CanAchieveKMoves(s, moves)
  ensures forall k :: k > moves ==> !CanAchieveKMoves(s, k)
{
  var openCount := new int[2];
  openCount[0] := 0;
  openCount[1] := 0;
  moves := 0;
  var j := 0;
  while j < |s|
  {
    var c := s[j];
    var i := if c == '[' || c == ']' then 1 else 0;
    if c == '(' || c == '[' {
      openCount[i] := openCount[i] + 1;
    } else if openCount[i] > 0 {
      openCount[i] := openCount[i] - 1;
      moves := moves + 1;
    }
    j := j + 1;
  }
}
// Egg Drop Problem (DP)
// Task: Add loop invariants so that Dafny can verify this program.

function Min(a: int, b: int): int { if a <= b then a else b }
function Max(a: int, b: int): int { if a >= b then a else b }

// EggDrop(e, f) = minimum number of trials to find critical floor
// with e eggs and f floors
function EggDropSpec(e: int, f: int): int
  requires e >= 1 && f >= 0
  decreases e + f
{
  if f <= 1 then f
  else if e == 1 then f
  else EggDropMin(e, f, 1, f)
}

function EggDropMin(e: int, f: int, x: int, best: int): int
  requires e >= 2 && f >= 2 && 1 <= x <= f
  requires best >= 0
  decreases f - x
{
  var trial := 1 + Max(EggDropSpec(e - 1, x - 1), EggDropSpec(e, f - x));
  var newBest := Min(best, trial);
  if x == f then newBest
  else EggDropMin(e, f, x + 1, newBest)
}

method EggDrop(eggs: int, floors: int) returns (result: int)
  requires eggs >= 1 && floors >= 0
  ensures result >= 0
{
  if floors <= 1 { return floors; }
  if eggs == 1 { return floors; }

  var dp := new int[eggs + 1, floors + 1];
  var e := 0;
  while e <= eggs
  {
    dp[e, 0] := 0;
    if floors >= 1 { dp[e, 1] := 1; }
    e := e + 1;
  }
  var f := 0;
  while f <= floors
  {
    dp[1, f] := f;
    f := f + 1;
  }

  e := 2;
  while e <= eggs
  {
    f := 2;
    while f <= floors
    {
      dp[e, f] := f; // worst case: 1 egg
      var x := 1;
      while x <= f
      {
        var trials := 1 + Max(dp[e-1, x-1], dp[e, f-x]);
        dp[e, f] := Min(dp[e, f], trials);
        x := x + 1;
      }
      f := f + 1;
    }
    e := e + 1;
  }
  result := dp[eggs, floors];
}

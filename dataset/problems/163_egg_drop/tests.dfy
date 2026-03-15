// Egg Drop Problem -- Spec tests

function Min(a: int, b: int): int { if a <= b then a else b }
function Max(a: int, b: int): int { if a >= b then a else b }

method EggDrop(eggs: int, floors: int) returns (result: int)
  requires eggs >= 1 && floors >= 0
  ensures result >= 0
{
  if floors <= 1 { return floors; }
  if eggs == 1 { return floors; }
  var dp := new int[eggs + 1, floors + 1];
  var e := 0;
  while e <= eggs invariant 0 <= e <= eggs + 1 invariant forall i, j :: 0 <= i < e && 0 <= j <= floors ==> dp[i,j] >= 0 decreases eggs + 1 - e {
    var f := 0;
    while f <= floors invariant 0 <= f <= floors + 1 invariant forall i, j :: 0 <= i < e && 0 <= j <= floors ==> dp[i,j] >= 0 invariant forall j :: 0 <= j < f ==> dp[e,j] >= 0 decreases floors + 1 - f {
      dp[e, f] := f; f := f + 1;
    }
    e := e + 1;
  }
  e := 2;
  while e <= eggs invariant 2 <= e <= eggs + 1 invariant forall i, j :: 0 <= i <= eggs && 0 <= j <= floors ==> dp[i,j] >= 0 decreases eggs + 1 - e {
    var f := 2;
    while f <= floors invariant 2 <= f <= floors + 1 invariant forall i, j :: 0 <= i <= eggs && 0 <= j <= floors ==> dp[i,j] >= 0 decreases floors + 1 - f {
      dp[e, f] := f;
      var x := 1;
      while x <= f invariant 1 <= x <= f + 1 invariant dp[e,f] >= 0 invariant forall i, j :: 0 <= i <= eggs && 0 <= j <= floors && (i != e || j != f) ==> dp[i,j] >= 0 decreases f + 1 - x {
        dp[e, f] := Min(dp[e, f], 1 + Max(dp[e-1, x-1], dp[e, f-x]));
        x := x + 1;
      }
      f := f + 1;
    }
    e := e + 1;
  }
  result := dp[eggs, floors];
}

method Main() {
  var r1 := EggDrop(2, 6);
  expect r1 == 3;

  var r2 := EggDrop(2, 10);
  expect r2 == 4;

  var r3 := EggDrop(1, 5);
  expect r3 == 5;

  var r4 := EggDrop(3, 0);
  expect r4 == 0;

  var r5 := EggDrop(3, 1);
  expect r5 == 1;

  expect r1 >= 0;

  print "All spec tests passed\n";
}

// The set of TV volumes reachable from `start` in at most `steps` button presses,
// where each press changes volume by one of {-5, -2, -1, +1, +2, +5}
// and the volume must remain non-negative after every press.
ghost function ReachableIn(start: int, steps: int): set<int>
  requires start >= 0
  requires steps >= 0
  decreases steps
{
  if steps == 0 then
    {start}
  else
    var prev := ReachableIn(start, steps - 1);
    prev + set v <- prev, d <- {-5, -2, -1, 1, 2, 5} | v + d >= 0 :: v + d
}

method ChangingVolume(a: int, b: int) returns (presses: int)
  requires a >= 0 && b >= 0
  ensures presses >= 0
  ensures b in ReachableIn(a, presses)
  ensures presses > 0 ==> b !in ReachableIn(a, presses - 1)
{
  var diff := if a > b then a - b else b - a;
  var fives := diff / 5;
  diff := diff % 5;
  var twos := diff / 2;
  diff := diff % 2;
  var ones := diff;
  presses := fives + twos + ones;
}
ghost function Pow(base: nat, exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else base * Pow(base, exp - 1)
}

// Who wins a fight between heroes i and j?
// Returns winner's index, or -1 on tie (equal levels).
ghost function FightWinner(levels: seq<int>, i: int, j: int): int
  requires 0 <= i < |levels| && 0 <= j < |levels| && i != j
{
  if levels[i] > levels[j] then i
  else if levels[j] > levels[i] then j
  else -1
}

// State after a fight: winner's level increases by 1; tie leaves state unchanged.
ghost function AfterFight(levels: seq<int>, i: int, j: int): (result: seq<int>)
  requires 0 <= i < |levels| && 0 <= j < |levels| && i != j
  ensures |result| == |levels|
{
  var w := FightWinner(levels, i, j);
  if w >= 0 then levels[w := levels[w] + 1] else levels
}

// Can hero h accumulate at least winsNeeded victories starting from levels,
// over a fight sequence of at most fuel total fights?
// Each step: choose any two distinct heroes to fight.
ghost predicate CanAccumulateWins(levels: seq<int>, h: int, winsNeeded: nat, fuel: nat)
  requires |levels| >= 2
  requires 0 <= h < |levels|
  decreases fuel
{
  winsNeeded == 0
  ||
  (fuel > 0 &&
   exists i, j | 0 <= i < |levels| && 0 <= j < |levels| && i != j ::
     var w := FightWinner(levels, i, j);
     var newLevels := AfterFight(levels, i, j);
     var gained: nat := if w == h then 1 else 0;
     CanAccumulateWins(newLevels, h, winsNeeded - gained, fuel - 1))
}

// A hero is a possible winner if there exists a sequence of fights
// in which they accumulate at least 100^500 wins.
ghost predicate IsPossibleWinner(levels: seq<int>, h: int)
  requires |levels| >= 2
  requires 0 <= h < |levels|
{
  exists fuel: nat :: CanAccumulateWins(levels, h, Pow(100, 500), fuel)
}

ghost function CountPossibleWinners(levels: seq<int>): int
  requires |levels| >= 2
{
  CountPossibleWinnersHelper(levels, |levels|)
}

ghost function CountPossibleWinnersHelper(levels: seq<int>, k: int): int
  requires |levels| >= 2
  requires 0 <= k <= |levels|
  decreases k
{
  if k == 0 then 0
  else
    (if IsPossibleWinner(levels, k - 1) then 1 else 0) +
    CountPossibleWinnersHelper(levels, k - 1)
}

method Arena(n: int, a: seq<int>) returns (count: int)
  requires |a| >= 2
  ensures count == CountPossibleWinners(a)
{
  var min_hero := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < min_hero {
      min_hero := a[i];
    }
    i := i + 1;
  }
  count := 0;
  i := 0;
  while i < |a|
  {
    if a[i] > min_hero {
      count := count + 1;
    }
    i := i + 1;
  }
}
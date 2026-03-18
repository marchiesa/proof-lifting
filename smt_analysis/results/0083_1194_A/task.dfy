ghost function InitialList(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else InitialList(n - 1) + [n]
}

ghost function RemoveAtIndex(s: seq<int>, idx: nat): seq<int>
  requires idx < |s|
{
  s[..idx] + s[idx + 1..]
}

// Simulate the removal algorithm: at each step, remove the step-th
// remaining element (1-indexed). Stop when fewer than step elements remain.
ghost function Simulate(remaining: seq<int>, step: nat): seq<int>
  decreases |remaining|
{
  if step == 0 || step > |remaining| then remaining
  else Simulate(RemoveAtIndex(remaining, step - 1), step + 1)
}

ghost function FinalList(n: nat): seq<int>
{
  Simulate(InitialList(n), 1)
}

method RemoveAProgression(n: int, x: int) returns (result: int)
  requires n >= 1
  requires x >= 1
  requires x <= |FinalList(n)|
  ensures result == FinalList(n)[x - 1]
{
  return x * 2;
}
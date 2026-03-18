ghost predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// 2^n, used to bound the plan space
ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Extract bit i from plan to determine target character at position i
ghost function TargetChar(plan: nat, i: nat): char
{
  if (plan / Pow2(i)) % 2 == 0 then '0' else '1'
}

// Cost of one position: flip cost (h if changed) + buy cost (c0 or c1)
ghost function CharCost(orig: char, target: char, c0: int, c1: int, h: int): int
{
  var buyCost := if target == '0' then c0 else c1;
  var flipCost := if orig != target then h else 0;
  buyCost + flipCost
}

// Total cost of a plan applied to the entire string
ghost function PlanCost(s: string, plan: nat, c0: int, c1: int, h: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else PlanCost(s[..|s|-1], plan, c0, c1, h) +
       CharCost(s[|s|-1], TargetChar(plan, |s|-1), c0, c1, h)
}

// cost is minimum: some plan achieves it, and no plan does better
ghost predicate IsMinCost(s: string, c0: int, c1: int, h: int, cost: int)
{
  (exists plan: nat :: PlanCost(s, plan, c0, c1, h) == cost)
  &&
  (forall plan: nat :: PlanCost(s, plan, c0, c1, h) >= cost)
}

method BuyTheString(s: string, c0: int, c1: int, h: int) returns (cost: int)
  requires IsBinaryString(s)
  ensures IsMinCost(s, c0, c1, h, cost)
{
  var ec1 := if c1 < h + c0 then c1 else h + c0;
  var ec0 := if c0 < h + ec1 then c0 else h + ec1;
  var count0 := 0;
  var count1 := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '0' {
      count0 := count0 + 1;
    } else {
      count1 := count1 + 1;
    }
    i := i + 1;
  }
  cost := count0 * ec0 + count1 * ec1;
}
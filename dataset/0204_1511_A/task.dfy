datatype ServerState = ServerState(up1: int, down1: int, up2: int, down2: int)

// Models one reviewer voting: type 1 upvotes, type 2 downvotes,
// type 3 checks the server's current counts (downvotes > upvotes → downvote, else upvote)
ghost function ProcessReviewer(state: ServerState, reviewerType: int, goToServer2: bool): ServerState
{
  if !goToServer2 then
    if reviewerType == 1 then ServerState(state.up1 + 1, state.down1, state.up2, state.down2)
    else if reviewerType == 2 then ServerState(state.up1, state.down1 + 1, state.up2, state.down2)
    else if state.down1 > state.up1 then ServerState(state.up1, state.down1 + 1, state.up2, state.down2)
    else ServerState(state.up1 + 1, state.down1, state.up2, state.down2)
  else
    if reviewerType == 1 then ServerState(state.up1, state.down1, state.up2 + 1, state.down2)
    else if reviewerType == 2 then ServerState(state.up1, state.down1, state.up2, state.down2 + 1)
    else if state.down2 > state.up2 then ServerState(state.up1, state.down1, state.up2, state.down2 + 1)
    else ServerState(state.up1, state.down1, state.up2 + 1, state.down2)
}

// Simulate all reviewers in order; each bit of mask assigns the corresponding reviewer to a server
ghost function Simulate(r: seq<int>, mask: int): ServerState
  requires mask >= 0
  decreases |r|
{
  if |r| == 0 then ServerState(0, 0, 0, 0)
  else
    var prev := Simulate(r[..|r|-1], mask / 2);
    ProcessReviewer(prev, r[|r|-1], mask % 2 == 1)
}

// Total upvotes across both servers for a given server-assignment mask
ghost function TotalUpvotes(r: seq<int>, mask: int): int
  requires mask >= 0
{
  var s := Simulate(r, mask);
  s.up1 + s.up2
}

ghost function Pow2(n: int): int
  requires n >= 0
  ensures Pow2(n) >= 1
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Maximum total upvotes over all assignment masks from 0 to bound (inclusive)
ghost function MaxUpvotesOver(r: seq<int>, bound: int): int
  requires bound >= 0
  decreases bound
{
  var curr := TotalUpvotes(r, bound);
  if bound == 0 then curr
  else
    var prev := MaxUpvotesOver(r, bound - 1);
    if curr > prev then curr else prev
}

// The optimal total upvotes achievable over all possible server assignment strategies
ghost function BestUpvotes(r: seq<int>): int
{
  MaxUpvotesOver(r, Pow2(|r|) - 1)
}

method ReviewSite(n: int, r: seq<int>) returns (maxUpvotes: int)
  requires n == |r|
  requires forall i | 0 <= i < |r| :: r[i] == 1 || r[i] == 2 || r[i] == 3
  ensures maxUpvotes == BestUpvotes(r)
{
  var count := 0;
  var i := 0;
  while i < |r|
  {
    if r[i] == 1 || r[i] == 3 {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}
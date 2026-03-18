datatype ServerState = ServerState(up1: int, down1: int, up2: int, down2: int)

function ProcessReviewer(state: ServerState, reviewerType: int, goToServer2: bool): ServerState
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

function Simulate(r: seq<int>, mask: int): ServerState
  requires mask >= 0
  decreases |r|
{
  if |r| == 0 then ServerState(0, 0, 0, 0)
  else
    var prev := Simulate(r[..|r|-1], mask / 2);
    ProcessReviewer(prev, r[|r|-1], mask % 2 == 1)
}

function TotalUpvotes(r: seq<int>, mask: int): int
  requires mask >= 0
{
  var s := Simulate(r, mask);
  s.up1 + s.up2
}

function Pow2(n: int): int
  requires n >= 0
  ensures Pow2(n) >= 1
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function MaxUpvotesOver(r: seq<int>, bound: int): int
  requires bound >= 0
  decreases bound
{
  var curr := TotalUpvotes(r, bound);
  if bound == 0 then curr
  else
    var prev := MaxUpvotesOver(r, bound - 1);
    if curr > prev then curr else prev
}

function BestUpvotes(r: seq<int>): int
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

method Main()
{
  // ========== SPEC POSITIVE TESTS (small inputs, length 1-3) ==========
  // From Test 1 case 1 / Test 3: r=[2] -> 0
  expect BestUpvotes([2]) == 0, "spec positive 1";
  // From Test 1 case 2: r=[1,2,3] -> 2
  expect BestUpvotes([1,2,3]) == 2, "spec positive 2";
  // From Test 1 case 4: r=[3,3,2] -> 2
  expect BestUpvotes([3,3,2]) == 2, "spec positive 3";
  // From Test 2 / Test 4: r=[1] -> 1
  expect BestUpvotes([1]) == 1, "spec positive 4";
  // From Test 5: r=[3] -> 1
  expect BestUpvotes([3]) == 1, "spec positive 5";
  // From Test 6: r=[3,3,3] -> 3
  expect BestUpvotes([3,3,3]) == 3, "spec positive 6";

  // ========== SPEC NEGATIVE TESTS (small inputs, length 1-3) ==========
  // From Negative 1 (first sub-case): r=[2], wrong=1
  expect BestUpvotes([2]) != 1, "spec negative 1";
  // From Negative 2 (first sub-case): r=[1], wrong=2
  expect BestUpvotes([1]) != 2, "spec negative 2";
  // From Negative 3: r=[2], wrong=1
  expect BestUpvotes([2]) != 1, "spec negative 3";
  // From Negative 4: r=[1], wrong=2
  expect BestUpvotes([1]) != 2, "spec negative 4";
  // From Negative 5: r=[3], wrong=2
  expect BestUpvotes([3]) != 2, "spec negative 5";
  // From Negative 6: r=[3,3,3], wrong=4
  expect BestUpvotes([3,3,3]) != 4, "spec negative 6";

  // ========== IMPLEMENTATION TESTS (full-size inputs) ==========
  // Test 1, case 1: r=[2] -> 0
  var r1 := ReviewSite(1, [2]);
  expect r1 == 0, "impl test 1 failed";

  // Test 1, case 2: r=[1,2,3] -> 2
  var r2 := ReviewSite(3, [1, 2, 3]);
  expect r2 == 2, "impl test 2 failed";

  // Test 1, case 3: r=[1,1,1,1,1] -> 5
  var r3 := ReviewSite(5, [1, 1, 1, 1, 1]);
  expect r3 == 5, "impl test 3 failed";

  // Test 1, case 4: r=[3,3,2] -> 2
  var r4 := ReviewSite(3, [3, 3, 2]);
  expect r4 == 2, "impl test 4 failed";

  // Test 2: r=[1] -> 1
  var r5 := ReviewSite(1, [1]);
  expect r5 == 1, "impl test 5 failed";

  // Test 3: r=[2] -> 0
  var r6 := ReviewSite(1, [2]);
  expect r6 == 0, "impl test 6 failed";

  // Test 4: r=[1] -> 1
  var r7 := ReviewSite(1, [1]);
  expect r7 == 1, "impl test 7 failed";

  // Test 5: r=[3] -> 1
  var r8 := ReviewSite(1, [3]);
  expect r8 == 1, "impl test 8 failed";

  // Test 6: r=[3,3,3] -> 3
  var r9 := ReviewSite(3, [3, 3, 3]);
  expect r9 == 3, "impl test 9 failed";

  // Test 7: r=[1,2,3,1,2] -> 3
  var r10 := ReviewSite(5, [1, 2, 3, 1, 2]);
  expect r10 == 3, "impl test 10 failed";

  // Test 8: r=[3,3,3,3,3,3,3] -> 7
  var r11 := ReviewSite(7, [3, 3, 3, 3, 3, 3, 3]);
  expect r11 == 7, "impl test 11 failed";

  // Test 9: r=[1,1,1,2,2,2,3,3,3,3] -> 7
  var r12 := ReviewSite(10, [1, 1, 1, 2, 2, 2, 3, 3, 3, 3]);
  expect r12 == 7, "impl test 12 failed";

  // Test 10: r=[2,2,2,3,3,3] -> 3
  var r13 := ReviewSite(6, [2, 2, 2, 3, 3, 3]);
  expect r13 == 3, "impl test 13 failed";

  // Test 11: r=[3,1,3,2,3,1,3,2] -> 6
  var r14 := ReviewSite(8, [3, 1, 3, 2, 3, 1, 3, 2]);
  expect r14 == 6, "impl test 14 failed";

  // Test 12: r=[2,3,1,3] -> 3
  var r15 := ReviewSite(4, [2, 3, 1, 3]);
  expect r15 == 3, "impl test 15 failed";

  print "All tests passed\n";
}
// Shared recursive function used by all examples
function segmentSum(s: seq<int>): int
{
  if |s| == 0 then 0
  else segmentSum(s[..|s|-1]) + s[|s|-1]
}

// =============================================================================
// EXAMPLE 1: One addition — without assert (FAILS)
// =============================================================================
// Z3 cannot prove this because the Seq#Equal ground term for
// nums[..i+1][..i] == nums[..i] is never created, so the extensionality
// axiom chain never fires.
method sumOne_NoAssert(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i < |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+1])
{
  sum2 := sum + nums[i];
}

// =============================================================================
// EXAMPLE 2: One addition — with assert (VERIFIES)
// =============================================================================
// The assert creates the Seq#Equal(nums[..i+1][..i], nums[..i]) ground term.
// This triggers: Seq#Equal definition → element-wise check → Seq#Equal(a,b) ==> a == b
// → sort-level equality → congruence closure equates segmentSum terms.
method sumOne_WithAssert(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i < |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+1])
{
  sum2 := sum + nums[i];
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];
}

// =============================================================================
// EXAMPLE 3: Three additions — without assert (FAILS)
// =============================================================================
// Same trigger gap as Example 1, but three times over.
method sumThree_NoAssert(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  sum2 := sum + nums[i];
  sum2 := sum2 + nums[i+1];
  sum2 := sum2 + nums[i+2];
}

// =============================================================================
// EXAMPLE 4: Three additions — 3 seq asserts only (FAILS)
// =============================================================================
// The seq equality asserts close the trigger gap, but default fuel (2)
// is not enough for 3 unfoldings. Z3 can unfold segmentSum twice but
// needs 3 steps to reach the precondition.
method sumThree_SeqOnly(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  sum2 := sum + nums[i];
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];

  sum2 := sum2 + nums[i+1];
  assert nums[..i+2][..|nums[..i+2]|-1] == nums[..i+1];

  sum2 := sum2 + nums[i+2];
  assert nums[..i+3][..|nums[..i+3]|-1] == nums[..i+2];
}

// =============================================================================
// EXAMPLE 5: Three additions — 3 seq asserts + 1 sum checkpoint (VERIFIES)
// =============================================================================
// The sum checkpoint after step 1 resets the fuel budget. With fuel 2,
// Z3 can handle 2 steps at a time: steps 1 (checkpoint resets), then 2+3.
method sumThree_SeqPlusCheckpoint(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  sum2 := sum + nums[i];
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];
  assert sum2 == segmentSum(nums[..i+1]);  // checkpoint — resets fuel

  sum2 := sum2 + nums[i+1];
  assert nums[..i+2][..|nums[..i+2]|-1] == nums[..i+1];

  sum2 := sum2 + nums[i+2];
  assert nums[..i+3][..|nums[..i+3]|-1] == nums[..i+2];
}

// =============================================================================
// EXAMPLE 6: Three additions — fuel 4 + 3 seq asserts (VERIFIES)
// =============================================================================
// {:fuel segmentSum, 4} gives 4 unfolding levels, enough for 3 steps.
// The seq asserts still needed to close the trigger gap at each step.
method {:fuel segmentSum, 4} sumThree_FuelPlusSeq(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  sum2 := sum + nums[i];
  assert nums[..i+1][..|nums[..i+1]|-1] == nums[..i];

  sum2 := sum2 + nums[i+1];
  assert nums[..i+2][..|nums[..i+2]|-1] == nums[..i+1];

  sum2 := sum2 + nums[i+2];
  assert nums[..i+3][..|nums[..i+3]|-1] == nums[..i+2];
}

// =============================================================================
// EXAMPLE 7: Three additions — fuel 4 only, no asserts (FAILS)
// =============================================================================
// Extra fuel alone is not enough — the trigger gap (missing Seq#Equal
// ground terms) is independent of the fuel issue.
method {:fuel segmentSum, 4} sumThree_FuelOnly(nums: seq<int>, i: int, sum: int) returns (sum2: int)
  requires 0 <= i
  requires i + 3 <= |nums|
  requires sum == segmentSum(nums[..i])
  ensures sum2 == segmentSum(nums[..i+3])
{
  sum2 := sum + nums[i];
  sum2 := sum2 + nums[i+1];
  sum2 := sum2 + nums[i+2];
}

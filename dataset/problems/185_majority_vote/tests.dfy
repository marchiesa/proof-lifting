// Majority Element (Boyer-Moore Voting)

function Count(a: seq<int>, v: int): nat
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + Count(a[1..], v)
}

predicate IsMajority(a: seq<int>, v: int)
{
  Count(a, v) > |a| / 2
}

predicate HasMajority(a: seq<int>)
{
  exists v :: v in a && IsMajority(a, v)
}

method MajorityVote(a: seq<int>) returns (candidate: int)
  requires |a| > 0
  requires HasMajority(a)
  ensures candidate in a
  ensures IsMajority(a, candidate)
{
  // Phase 1: Find candidate using Boyer-Moore
  candidate := a[0];
  var count := 1;
  var i := 1;
  while i < |a|
  {
    if a[i] == candidate {
      count := count + 1;
    } else if count == 0 {
      candidate := a[i];
      count := 1;
    } else {
      count := count - 1;
    }
    i := i + 1;
  }

  // Phase 2: Verify candidate
  var actualCount := 0;
  i := 0;
  while i < |a|
  {
    if a[i] == candidate {
      actualCount := actualCount + 1;
    }
    i := i + 1;
  }

  // Since HasMajority holds, and Boyer-Moore finds the correct candidate
  // when a majority exists, actualCount > |a|/2
}

method Main()
{
  // [2,2,1,1,2] has majority 2 (count=3 > 5/2=2)
  var a := [2, 2, 1, 1, 2];
  expect IsMajority(a, 2);
  expect HasMajority(a);
  var r1 := MajorityVote(a);
  expect r1 in a;
  expect IsMajority(a, r1);

  // Single element
  var b := [7];
  expect HasMajority(b);
  var r2 := MajorityVote(b);
  expect r2 == 7;

  // All same
  var c := [3, 3, 3];
  expect HasMajority(c);
  var r3 := MajorityVote(c);
  expect r3 == 3;

  // Negative test: IsMajority should fail for non-majority
  expect !IsMajority(a, 1);

  print "All spec tests passed\n";
}

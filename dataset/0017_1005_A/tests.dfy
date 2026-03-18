// Generates the counting sequence [1, 2, ..., n]
function CountingSeq(n: int): seq<int>
  decreases n
{
  if n <= 0 then [] else CountingSeq(n - 1) + [n]
}

// Every element is at least 1 (each stairway has at least one step)
predicate AllPositive(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 1
}

// Concatenates counting sequences: [1..stairs[0]] ++ [1..stairs[1]] ++ ...
function ConcatStairways(stairs: seq<int>): seq<int>
  decreases |stairs|
{
  if |stairs| == 0 then []
  else ConcatStairways(stairs[..|stairs|-1]) + CountingSeq(stairs[|stairs|-1])
}

// The input is a valid pronunciation: starts at 1, each next element
// either starts a new stairway (== 1) or continues the count (== prev + 1)
predicate IsValidInput(a: seq<int>)
{
  |a| >= 1 &&
  a[0] == 1 &&
  forall i | 1 <= i < |a| :: a[i] == 1 || a[i] == a[i - 1] + 1
}

// Combined postcondition: all ensures clauses together
predicate Postcondition(a: seq<int>, t: int, stairs: seq<int>)
{
  t == |stairs| && t >= 1 && AllPositive(stairs) && ConcatStairways(stairs) == a
}

method TanyaAndStairways(a: seq<int>) returns (t: int, stairs: seq<int>)
  requires IsValidInput(a)
  ensures t == |stairs|
  ensures t >= 1
  ensures AllPositive(stairs)
  ensures ConcatStairways(stairs) == a
{
  stairs := [];
  var cnt := 0;
  for i := 0 to |a| {
    if i == 0 {
      cnt := 1;
    } else if a[i] == 1 {
      stairs := stairs + [cnt];
      cnt := 1;
    } else {
      cnt := cnt + 1;
    }
  }
  stairs := stairs + [cnt];
  t := |stairs|;
}

method Main()
{
  // =============================================
  // SPEC POSITIVE TESTS (small inputs)
  // =============================================

  // From Test 5: a=[1], t=1, stairs=[1]
  expect Postcondition([1], 1, [1]), "spec positive 1";

  // From Test 7: a=[1,2], t=1, stairs=[2]
  expect Postcondition([1, 2], 1, [2]), "spec positive 2";

  // From Test 8: a=[1,1,2], t=2, stairs=[1,2]
  expect Postcondition([1, 1, 2], 2, [1, 2]), "spec positive 3";

  // From Test 9: a=[1,1,2,3], t=2, stairs=[1,3]
  expect Postcondition([1, 1, 2, 3], 2, [1, 3]), "spec positive 4";

  // Scaled from Test 2: a=[1,1,1], t=3, stairs=[1,1,1]
  expect Postcondition([1, 1, 1], 3, [1, 1, 1]), "spec positive 5";

  // Scaled from Test 4: a=[1,2,1], t=2, stairs=[2,1]
  expect Postcondition([1, 2, 1], 2, [2, 1]), "spec positive 6";

  // Scaled from Test 3: a=[1,2,3], t=1, stairs=[3]
  expect Postcondition([1, 2, 3], 1, [3]), "spec positive 7";

  // =============================================
  // SPEC NEGATIVE TESTS (small inputs)
  // =============================================

  // From Neg 5: a=[1], wrong t=2, stairs=[1]
  expect !Postcondition([1], 2, [1]), "spec negative 1";

  // From Neg 7: a=[1,2], wrong t=2, stairs=[2]
  expect !Postcondition([1, 2], 2, [2]), "spec negative 2";

  // From Neg 8: a=[1,1,2], wrong t=3, stairs=[1,2]
  expect !Postcondition([1, 1, 2], 3, [1, 2]), "spec negative 3";

  // From Neg 9: a=[1,1,2,3], wrong t=3, stairs=[1,3]
  expect !Postcondition([1, 1, 2, 3], 3, [1, 3]), "spec negative 4";

  // Scaled from Neg 1: a=[1,2,3], wrong t=2, stairs=[3]
  expect !Postcondition([1, 2, 3], 2, [3]), "spec negative 5";

  // Scaled from Neg 2: a=[1,1,1], wrong t=4, stairs=[1,1,1]
  expect !Postcondition([1, 1, 1], 4, [1, 1, 1]), "spec negative 6";

  // Scaled from Neg 4: a=[1,2,1], wrong t=3, stairs=[2,1]
  expect !Postcondition([1, 2, 1], 3, [2, 1]), "spec negative 7";

  // =============================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // =============================================

  var t1, s1 := TanyaAndStairways([1, 2, 3, 1, 2, 3, 4]);
  expect t1 == 2, "impl test 1: t mismatch";
  expect s1 == [3, 4], "impl test 1: stairs mismatch";

  var t2, s2 := TanyaAndStairways([1, 1, 1, 1]);
  expect t2 == 4, "impl test 2: t mismatch";
  expect s2 == [1, 1, 1, 1], "impl test 2: stairs mismatch";

  var t3, s3 := TanyaAndStairways([1, 2, 3, 4, 5]);
  expect t3 == 1, "impl test 3: t mismatch";
  expect s3 == [5], "impl test 3: stairs mismatch";

  var t4, s4 := TanyaAndStairways([1, 2, 1, 2, 1]);
  expect t4 == 3, "impl test 4: t mismatch";
  expect s4 == [2, 2, 1], "impl test 4: stairs mismatch";

  var t5, s5 := TanyaAndStairways([1]);
  expect t5 == 1, "impl test 5: t mismatch";
  expect s5 == [1], "impl test 5: stairs mismatch";

  var t6, s6 := TanyaAndStairways([1, 2, 3, 4, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 2, 3, 4, 1, 2, 3, 4, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1]);
  expect t6 == 20, "impl test 6: t mismatch";
  expect s6 == [4, 3, 1, 3, 4, 1, 4, 4, 4, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 1], "impl test 6: stairs mismatch";

  var t7, s7 := TanyaAndStairways([1, 2]);
  expect t7 == 1, "impl test 7: t mismatch";
  expect s7 == [2], "impl test 7: stairs mismatch";

  var t8, s8 := TanyaAndStairways([1, 1, 2]);
  expect t8 == 2, "impl test 8: t mismatch";
  expect s8 == [1, 2], "impl test 8: stairs mismatch";

  var t9, s9 := TanyaAndStairways([1, 1, 2, 3]);
  expect t9 == 2, "impl test 9: t mismatch";
  expect s9 == [1, 3], "impl test 9: stairs mismatch";

  var t10, s10 := TanyaAndStairways([1, 2, 3, 1, 2, 3, 4, 5]);
  expect t10 == 2, "impl test 10: t mismatch";
  expect s10 == [3, 5], "impl test 10: stairs mismatch";

  var t11, s11 := TanyaAndStairways([1, 1, 1, 2, 3]);
  expect t11 == 3, "impl test 11: t mismatch";
  expect s11 == [1, 1, 3], "impl test 11: stairs mismatch";

  print "All tests passed\n";
}
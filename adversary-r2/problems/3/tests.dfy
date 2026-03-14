// Tests for Problem 3: Edit Distance
include "task.dfy"

method Main()
{
  // Test 1: Same strings
  var s1: seq<int> := [1, 2, 3];
  var t1: seq<int> := [1, 2, 3];
  var r1 := EditDistance(s1, t1);
  print "Test 1 - EditDistance([1,2,3], [1,2,3]): ", r1, " (expected 0)\n";

  // Test 2: Completely different (same length)
  var s2: seq<int> := [1, 2, 3];
  var t2: seq<int> := [4, 5, 6];
  var r2 := EditDistance(s2, t2);
  print "Test 2 - EditDistance([1,2,3], [4,5,6]): ", r2, " (expected 3)\n";

  // Test 3: One empty
  var s3: seq<int> := [1, 2, 3];
  var t3: seq<int> := [];
  var r3 := EditDistance(s3, t3);
  print "Test 3 - EditDistance([1,2,3], []): ", r3, " (expected 3)\n";

  // Test 4: Both empty
  var s4: seq<int> := [];
  var t4: seq<int> := [];
  var r4 := EditDistance(s4, t4);
  print "Test 4 - EditDistance([], []): ", r4, " (expected 0)\n";

  // Test 5: Classic "kitten" -> "sitting" analogy
  // Using integer encoding: k=1,i=2,t=3,t=3,e=4,n=5 -> s=6,i=2,t=3,t=3,i=2,n=5,g=7
  // k->s (replace), e->i (replace), +g (insert) = 3
  var s5: seq<int> := [1, 2, 3, 3, 4, 5];
  var t5: seq<int> := [6, 2, 3, 3, 2, 5, 7];
  var r5 := EditDistance(s5, t5);
  print "Test 5 - EditDistance('kitten','sitting'): ", r5, " (expected 3)\n";

  // Test 6: Insert only
  var s6: seq<int> := [1, 3];
  var t6: seq<int> := [1, 2, 3];
  var r6 := EditDistance(s6, t6);
  print "Test 6 - EditDistance([1,3], [1,2,3]): ", r6, " (expected 1)\n";
}

// Find Second Maximum -- Runtime spec tests

predicate IsMax(val: int, s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] <= val
}

predicate ExistsIn(val: int, s: seq<int>)
{
  exists i | 0 <= i < |s| :: s[i] == val
}

method Main() {
  // IsMax positive cases
  expect IsMax(9, [3, 1, 4, 1, 5, 9, 2, 6]), "9 is max of sequence";
  expect IsMax(5, [5, 5, 5]), "5 is max of all-fives";
  expect IsMax(20, [10, 20]), "20 is max of pair";
  expect IsMax(0, []), "any value is max of empty";
  expect IsMax(42, [42]), "singleton max";
  expect IsMax(100, [1, 2, 3]), "100 >= all in [1,2,3]";

  // IsMax negative cases
  expect !IsMax(5, [3, 1, 4, 1, 5, 9, 2, 6]), "5 is not max (9 exists)";
  expect !IsMax(1, [1, 2, 3]), "1 is not max of [1,2,3]";
  expect !IsMax(0, [1]), "0 is not max of [1]";

  // ExistsIn positive cases
  expect ExistsIn(3, [1, 2, 3, 4]), "3 exists in sequence";
  expect ExistsIn(1, [1]), "singleton exists";
  expect ExistsIn(5, [5, 5, 5]), "5 in all-fives";

  // ExistsIn negative cases
  expect !ExistsIn(10, [1, 2, 3]), "10 not in [1,2,3]";
  expect !ExistsIn(0, [1, 2, 3]), "0 not in [1,2,3]";
  expect !ExistsIn(1, []), "nothing in empty";

  print "All spec tests passed\n";
}

ghost function FriendSum(a1: int, a2: int, a3: int, a4: int,
                   b1: bool, b2: bool, b3: bool, b4: bool): int
{
  (if b1 then a1 else 0) + (if b2 then a2 else 0) +
  (if b3 then a3 else 0) + (if b4 then a4 else 0)
}

ghost predicate CanDistributeEqually(a1: int, a2: int, a3: int, a4: int)
{
  exists b1: bool, b2: bool, b3: bool, b4: bool ::
    FriendSum(a1, a2, a3, a4, b1, b2, b3, b4) ==
    FriendSum(a1, a2, a3, a4, !b1, !b2, !b3, !b4)
}

method DawidAndCandies(a1: int, a2: int, a3: int, a4: int) returns (result: bool)
  requires a1 >= 1 && a2 >= 1 && a3 >= 1 && a4 >= 1
  ensures result == CanDistributeEqually(a1, a2, a3, a4)
{
  result := (a1 + a2 == a3 + a4) || (a1 + a3 == a2 + a4) || (a1 + a4 == a2 + a3) ||
            (a1 + a2 + a3 == a4) || (a1 + a2 + a4 == a3) || (a1 + a3 + a4 == a2) || (a2 + a3 + a4 == a1);

  if result {
    if a1 + a2 == a3 + a4 {
      // PLACEHOLDER_0: insert assertion here

    } else if a1 + a3 == a2 + a4 {
      // PLACEHOLDER_1: insert assertion here

    } else if a1 + a4 == a2 + a3 {
      // PLACEHOLDER_2: insert assertion here

    } else if a1 + a2 + a3 == a4 {
      // PLACEHOLDER_3: insert assertion here

    } else if a1 + a2 + a4 == a3 {
      // PLACEHOLDER_4: insert assertion here

    } else if a1 + a3 + a4 == a2 {
      // PLACEHOLDER_5: insert assertion here

    } else {
      assert a2 + a3 + a4 == a1;
      // PLACEHOLDER_6: insert assertion here

    }
  }
}

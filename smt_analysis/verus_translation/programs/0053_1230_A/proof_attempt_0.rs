use vstd::prelude::*;

verus! {

spec fn FriendSum(a1: int, a2: int, a3: int, a4: int,
                  b1: bool, b2: bool, b3: bool, b4: bool) -> int
{
    (if b1 { a1 } else { 0 }) + (if b2 { a2 } else { 0 }) +
    (if b3 { a3 } else { 0 }) + (if b4 { a4 } else { 0 })
}

spec fn CanDistributeEqually(a1: int, a2: int, a3: int, a4: int) -> bool
{
    exists|b1: bool, b2: bool, b3: bool, b4: bool|
        #[trigger] FriendSum(a1, a2, a3, a4, b1, b2, b3, b4) ==
        FriendSum(a1, a2, a3, a4, !b1, !b2, !b3, !b4)
}

fn DawidAndCandies(a1: i64, a2: i64, a3: i64, a4: i64) -> (result: bool)
    requires
        a1 >= 1 && a2 >= 1 && a3 >= 1 && a4 >= 1,
    ensures
        result == CanDistributeEqually(a1 as int, a2 as int, a3 as int, a4 as int),
{
    let result = (a1 + a2 == a3 + a4) || (a1 + a3 == a2 + a4) || (a1 + a4 == a2 + a3) ||
                 (a1 + a2 + a3 == a4) || (a1 + a2 + a4 == a3) || (a1 + a3 + a4 == a2) ||
                 (a2 + a3 + a4 == a1);

    if result {
        if a1 + a2 == a3 + a4 {
            proof {
                assert(FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, true, true, false, false) ==
                       FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, false, false, true, true));
            }
        } else if a1 + a3 == a2 + a4 {
            proof {
                assert(FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, true, false, true, false) ==
                       FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, false, true, false, true));
            }
        } else if a1 + a4 == a2 + a3 {
            proof {
                assert(FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, true, false, false, true) ==
                       FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, false, true, true, false));
            }
        } else if a1 + a2 + a3 == a4 {
            proof {
                assert(FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, false, false, false, true) ==
                       FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, true, true, true, false));
            }
        } else if a1 + a2 + a4 == a3 {
            proof {
                assert(FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, false, false, true, false) ==
                       FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, true, true, false, true));
            }
        } else if a1 + a3 + a4 == a2 {
            proof {
                assert(FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, false, true, false, false) ==
                       FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, true, false, true, true));
            }
        } else {
            proof {
                assert(FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, true, false, false, false) ==
                       FriendSum(a1 as int, a2 as int, a3 as int, a4 as int, false, true, true, true));
            }
        }
    }
    result
}

fn main() {}

} // verus!
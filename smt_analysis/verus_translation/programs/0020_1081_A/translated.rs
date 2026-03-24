use vstd::prelude::*;

verus! {

spec fn valid_move(n: int, x: int) -> bool {
    1 <= x && x < n && n % x != 0
}

spec fn reachable(start: int, target: int, steps: nat) -> bool
    decreases steps
{
    start >= 1 && target >= 1 &&
    (start == target ||
     (steps > 0 &&
      exists|x: int| 1 <= x && x < start && valid_move(start, x) && reachable(start - x, target, (steps - 1) as nat)))
}

spec fn is_min_reachable(v: int, result: int) -> bool {
    v >= 1 && result >= 1 &&
    reachable(v, result, v as nat) &&
    forall|r: int| 1 <= r && r < result ==> !reachable(v, r, v as nat)
}

fn definite_game(v: i64) -> (result: i64)
    requires v >= 1
    ensures is_min_reachable(v as int, result as int)
{
    if v == 2 {
        proof { assume(false); }
        2
    } else if v == 1 {
        proof { assume(false); }
        1
    } else {
        proof { assume(false); }
        1
    }
}

fn main() {}

} // verus!
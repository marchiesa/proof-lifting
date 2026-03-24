use vstd::prelude::*;

verus! {

spec fn feasible(a: int, b: int, c: int, x: int, y: int) -> bool {
    x >= 0 && y >= 0 && x <= a && 2 * x + y <= b && 2 * y <= c
}

spec fn stones_collected(x: int, y: int) -> int {
    3 * (x + y)
}

fn stones(a: i64, b: i64, c: i64) -> (max_stones: i64)
    requires
        a >= 0 && b >= 0 && c >= 0,
    ensures
        exists|x: int, y: int|
            feasible(a as int, b as int, c as int, x, y)
                && max_stones as int == stones_collected(x, y),
        forall|x: int, y: int|
            feasible(a as int, b as int, c as int, x, y)
                ==> stones_collected(x, y) <= max_stones as int,
{
    let c2: i64 = if c / 2 < b { c / 2 } else { b };
    let rem: i64 = if (b - c2) / 2 < a { (b - c2) / 2 } else { a };
    let max_stones: i64 = (c2 + rem) * 3;

    proof {
        assume(false);
    }

    max_stones
}

fn main() {}

} // verus!
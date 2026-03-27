use vstd::prelude::*;

verus! {

spec fn valid_step(x: int, y: int) -> bool {
    x < y && y - x > 0
}

spec fn reachable(a: int, b: int) -> bool {
    exists|c: int| valid_step(a, c) && valid_step(c, b)
}

fn reach(a: i64, b: i64) -> (c: i64)
    requires a as int + 2 < b as int,
    ensures reachable(a as int, b as int),
{
    let c = a + 1;
    // TODO: add assertion here
    c
}

} // verus!

fn main() {}

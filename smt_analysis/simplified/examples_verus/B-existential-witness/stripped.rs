use vstd::prelude::*;

verus! {

spec fn p(x: int, y: int) -> bool {
    x > 0 && y == x * 2
}

fn m(n: i64) -> (r: i64)
    requires n >= 1, n <= 1_000_000_000,
    ensures exists|x: int| #[trigger] p(x, r as int),
{
    let r = n * 2;
    // TODO: add assertion here
    r
}

} // verus!

fn main() {}

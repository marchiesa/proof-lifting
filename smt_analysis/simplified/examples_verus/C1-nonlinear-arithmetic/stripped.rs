use vstd::prelude::*;

verus! {

fn m(n: i64) -> (r: i64)
    requires n >= 1, n <= 1_000_000_000,
    ensures r as int > 1,
        exists|d: int| 2 <= d <= r as int - 1 && #[trigger] (r as int % d) == 0,
{
    let r = n * 6;
    // TODO: add assertion here
    r
}

} // verus!

fn main() {}

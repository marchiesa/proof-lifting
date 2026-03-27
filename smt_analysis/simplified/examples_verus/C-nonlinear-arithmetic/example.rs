use vstd::prelude::*;

verus! {

fn m(n: i64) -> (r: i64)
    requires n >= 1, n <= 1_000_000_000,
    ensures r as int > 1,
        exists|d: int| 2 <= d <= r as int - 1 && #[trigger] (r as int % d) == 0,
{
    let r = n * 6;
    proof {
        assert(r as int % 3 == 0) by(nonlinear_arith)  // QUIRK: NLA
            requires r == n as int * 6;
    }
    r
}

} // verus!

fn main() {}

use vstd::prelude::*;

verus! {

spec fn IsComposite(x: int) -> bool {
    x > 1 && exists|d: int| 2 <= d <= x - 1 && #[trigger] (x % d) == 0
}

fn Equation(n: i64) -> (result: (i64, i64))
    requires
        n >= 1,
        n <= 1_000_000_000_000_000_000i64,
    ensures
        IsComposite(result.0 as int),
        IsComposite(result.1 as int),
        result.0 as int - (result.1 as int) == n as int,
{
    let a: i64 = n * 9;
    let b: i64 = n * 8;
    proof {
        // PLACEHOLDER_0: insert assertion here




        // PLACEHOLDER_1: insert assertion here




    }
    (a, b)
}

} // verus!

fn main() {}
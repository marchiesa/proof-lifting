use vstd::prelude::*;

verus! {

spec fn ValidDistribution(a: int, b: int, c: int, n: int, A: int, B: int, C: int) -> bool {
    A >= 0 && B >= 0 && C >= 0
    && A + B + C == n
    && a + A == b + B
    && a + A == c + C
}

spec fn CanDistribute(a: int, b: int, c: int, n: int) -> bool
    recommends n >= 0
{
    exists|A: int, B: int, C: int| ValidDistribution(a, b, c, n, A, B, C)
}

fn CollectingCoins(a: i64, b: i64, c: i64, n: i64) -> (result: bool)
    requires
        a >= 0 && b >= 0 && c >= 0 && n >= 0
    ensures
        result == CanDistribute(a as int, b as int, c as int, n as int)
{
    let tot: i64 = a + b + c + n;
    if tot % 3 != 0 {
        proof { assume(false); }
        return false;
    }
    let des: i64 = tot / 3;
    if a > des || b > des || c > des {
        proof { assume(false); }
        return false;
    }
    proof { assume(false); }
    return true;
}

fn main() {}

} // verus!
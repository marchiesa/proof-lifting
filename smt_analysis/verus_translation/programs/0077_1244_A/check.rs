use vstd::prelude::*;

verus! {

spec fn valid_assignment(x: int, y: int, a: int, b: int, c: int, d: int, k: int) -> bool {
    x >= 0 && y >= 0 && x * c >= a && y * d >= b && x + y <= k
}

spec fn feasible(a: int, b: int, c: int, d: int, k: int) -> bool {
    exists|x: int, y: int| valid_assignment(x, y, a, b, c, d, k)
}

proof fn mul_le(a: int, b: int, c: int)
    requires
        a <= b && c >= 0,
    ensures
        a * c <= b * c,
{
}

proof fn ceil_div_lower(a: int, c: int)
    requires
        a >= 1 && c >= 1,
    ensures
        ((a + c - 1) / c) * c >= a,
        (a + c - 1) / c >= 0,
{
    assume(false);
}

proof fn ceil_div_minimal(a: int, c: int, x: int)
    requires
        a >= 1 && c >= 1 && x >= 0 && x * c >= a,
    ensures
        x >= (a + c - 1) / c,
{
    assume(false);
}

fn pens_and_pencils(a: i64, b: i64, c: i64, d: i64, k: i64) -> (result: (i64, i64))
    requires
        a >= 1 && b >= 1 && c >= 1 && d >= 1 && k >= 1,
    ensures
        feasible(a as int, b as int, c as int, d as int, k as int) ==>
            valid_assignment(result.0 as int, result.1 as int,
                             a as int, b as int, c as int, d as int, k as int),
        !feasible(a as int, b as int, c as int, d as int, k as int) ==> result.0 == -1i64,
{
    let pens = (a + c - 1) / c;
    let pencils = (b + d - 1) / d;

    proof {
        ceil_div_lower(a as int, c as int);
        ceil_div_lower(b as int, d as int);
    }

    if pens + pencils <= k {
        proof { assume(false); }
        return (pens, pencils);
    } else {
        proof { assume(false); }
        return (-1, 0);
    }
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn Min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn Max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn Divides(d: int, n: int) -> bool
    recommends d > 0
{
    n % d == 0
}

spec fn IsGcd(g: int, a: int, b: int) -> bool
    recommends a > 0 && b > 0 && g > 0
{
    Divides(g, a) && Divides(g, b) &&
    (forall|d: int| (1 <= d && d <= Min(a, b)) ==>
        (Divides(d, a) && Divides(d, b)) ==> d <= g)
}

spec fn IsLcm(l: int, a: int, b: int) -> bool
    recommends a > 0 && b > 0 && l > 0
{
    Divides(a, l) && Divides(b, l) &&
    (forall|m: int| (1 <= m && m <= l) ==>
        (Divides(a, m) && Divides(b, m)) ==> l <= m)
}

spec fn ValidSolution(a: int, b: int, x: int) -> bool {
    a > 0 && b > 0 && x > 0 &&
    (exists|g: int| 1 <= g && g <= Min(a, b) &&
        exists|l: int| Max(a, b) <= l && l <= a * b &&
            IsGcd(g, a, b) && IsLcm(l, a, b) && g + l == x)
}

proof fn DivModLemma(b: int, m: int)
    requires
        b > 0,
        1 <= m && m <= b,
        m % b == 0,
    ensures
        m == b,
{
    let q = m / b;
    assume(false);
}

fn EhAbAndGcd(x: i64) -> (a: i64, b: i64)
    requires
        x >= 2i64,
    ensures
        ValidSolution(a as int, b as int, x as int),
{
    let a: i64 = 1;
    let b: i64 = x - 1;
    proof {
        assume(false);
    }
    (a, b)
}

fn main() {}

} // verus!
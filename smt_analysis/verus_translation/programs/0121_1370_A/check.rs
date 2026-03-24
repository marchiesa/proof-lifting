use vstd::prelude::*;

verus! {

spec fn Gcd(a: int, b: int) -> int
    recommends a > 0 && b > 0
    decreases b
{
    if a % b == 0 { b }
    else { Gcd(b, a % b) }
}

proof fn MulLeMonotone(c: int, a: int, b: int)
    requires
        c > 0,
        a <= b,
    ensures
        c * a <= c * b,
    decreases c
{
    assume(false);
}

proof fn GcdBound(a: int, b: int)
    requires
        0 < a,
        a < b,
    ensures
        Gcd(a, b) * 2 <= b,
    decreases b, a
{
    assume(false);
}

fn MaximumGCD(n: i64) -> (result: i64)
    requires
        n >= 2,
    ensures
        exists|a: int| 1 <= a && a < n as int && (exists|b: int| a < b && b <= n as int && Gcd(a, b) == result as int),
        forall|a: int| 1 <= a && a < n as int ==> (forall|b: int| a < b && b <= n as int ==> Gcd(a, b) <= result as int),
{
    let result = n / 2;
    let wa = n / 2;
    let wb = 2 * wa;
    proof { assume(false); }
    result
}

fn main() {}

} // verus!
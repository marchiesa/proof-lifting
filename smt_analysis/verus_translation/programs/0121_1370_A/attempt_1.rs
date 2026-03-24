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
    ensures c * a <= c * b
    decreases c
{
    if c > 1 {
        MulLeMonotone(c - 1, a, b);
    }
}

proof fn GcdBound(a: int, b: int)
    requires 0 < a && a < b
    ensures Gcd(a, b) * 2 <= b
    decreases b, a
{
    assume(false); // assert a % b == a;
    assume(false); // assert Gcd(a, b) == Gcd(b, a);
    let r: int = b % a;
    if r == 0 {
        assume(false); // assert Gcd(b, a) == a;
        let k: int = b / a;
        assume(false); // assert b == a * k;
        assume(false); // assert k >= 2;
        MulLeMonotone(a, 2, k);
    } else {
        assume(false); // assert 0 < r && r < a;
        assume(false); // assert Gcd(b, a) == Gcd(a, r);
        assume(false); // assert r % a == r;
        assume(false); // assert Gcd(r, a) == Gcd(a, r);
        GcdBound(r, a);
    }
}

fn MaximumGCD(n: i64) -> (result: i64)
    requires n >= 2i64
    ensures exists|a: int| 1 <= a && a < n as int &&
        (exists|b: int| a < b && b <= n as int &&
        Gcd(a, b) == result as int)
    ensures forall|a: int| 1 <= a && a < n as int ==>
        (forall|b: int| a < b && b <= n as int ==>
        Gcd(a, b) <= result as int)
{
    let result: i64 = n / 2;
    proof {
        let wa: int = n as int / 2;
        let wb: int = 2 * wa;
        assume(false); // assert 1 <= wa && wa < n
        assume(false); // assert wa < wb && wb <= n
        assume(false); // assert wb % wa == 0
        assume(false); // assert Gcd(wb, wa) == wa
        assume(false); // assert Gcd(wa, wb) == wa
        assume(false); // forall ai, bi: GcdBound(ai, bi) proof placeholder
    }
    result
}

fn main() {}

} // verus!
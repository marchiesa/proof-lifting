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
    if c > 1 {
        MulLeMonotone(c - 1, a, b);
    }
}

proof fn GcdBound(a: int, b: int)
    requires
        0 < a,
        a < b,
    ensures
        Gcd(a, b) * 2 <= b,
    decreases b, a
{
    assert(a % b == a);
    assert(Gcd(a, b) == Gcd(b, a));

    let r = b % a;
    if r == 0 {
        assert(Gcd(b, a) == a);
        let k = b / a;
        assert(b == a * k);
        assert(k >= 2);
        MulLeMonotone(a, 2, k);
    } else {
        assert(0 < r && r < a);
        assert(Gcd(b, a) == Gcd(a, r));
        assert(r % a == r);
        assert(Gcd(r, a) == Gcd(a, r));
        GcdBound(r, a);
    }
}

fn MaximumGCD(n: i64) -> (result: i64)
    requires
        n >= 2,
    ensures
        exists|a: int, b: int| #![trigger Gcd(a, b)] 1 <= a && a < n as int && a < b && b <= n as int && Gcd(a, b) == result as int,
        forall|a: int, b: int| #![trigger Gcd(a, b)] 1 <= a && a < n as int && a < b && b <= n as int ==> Gcd(a, b) <= result as int,
{
    let result = n / 2;
    let wa = n / 2;
    let wb = 2 * wa;

    proof {
        assert(1 <= wa as int && (wa as int) < n as int);
        assert((wa as int) < (wb as int) && (wb as int) <= n as int);
        assert((wb as int) % (wa as int) == 0);
        assert((wa as int) % (wb as int) == wa as int);
        assert(Gcd(wa as int, wb as int) == Gcd(wb as int, wa as int));
        assert(Gcd(wb as int, wa as int) == wa as int);
        assert(Gcd(wa as int, wb as int) == result as int);

        assert forall|ai: int, bi: int| #![trigger Gcd(ai, bi)] 1 <= ai && ai < n as int && ai < bi && bi <= n as int implies Gcd(ai, bi) <= result as int by {
            GcdBound(ai, bi);
        };
    }

    result
}

fn main() {}

} // verus!
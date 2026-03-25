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
    // Since a < b, a % b == a != 0, so Gcd(a, b) == Gcd(b, a)
    assert(a % b == a);
    assert(a % b != 0);
    assert(Gcd(a, b) == Gcd(b, a % b));
    assert(Gcd(a, b) == Gcd(b, a));

    let r: int = b % a;
    if r == 0 {
        // b % a == 0 => Gcd(b, a) == a
        assert(Gcd(b, a) == a);
        let k: int = b / a;
        assert(b == a * k);
        assert(k >= 2);
        MulLeMonotone(a, 2, k);
        // a * 2 <= a * k == b, and Gcd(a, b) == a
        assert(Gcd(a, b) * 2 <= b);
    } else {
        // 0 < r < a, so Gcd(b, a) == Gcd(a, r) and Gcd(r, a) == Gcd(a, r)
        assert(0 < r);
        assert(r < a);
        assert(b % a != 0);
        assert(Gcd(b, a) == Gcd(a, b % a));
        assert(Gcd(b, a) == Gcd(a, r));
        assert(r % a == r);
        assert(r % a != 0);
        assert(Gcd(r, a) == Gcd(a, r % a));
        assert(Gcd(r, a) == Gcd(a, r));
        assert(Gcd(a, b) == Gcd(r, a));
        // By induction: Gcd(r, a) * 2 <= a < b
        GcdBound(r, a);
        assert(Gcd(r, a) * 2 <= a);
        assert(Gcd(a, b) * 2 <= b);
    }
}

fn MaximumGCD(n: i64) -> (result: i64)
    requires
        n >= 2,
    ensures
        exists|a: int| 1 <= a && a < n as int && (exists|b: int| a < b && b <= n as int && #[trigger] Gcd(a, b) == result as int),
        forall|a: int, b: int| (1 <= a && a < n as int && a < b && b <= n as int) ==> #[trigger] Gcd(a, b) <= result as int,
{
    let result = n / 2;
    let wa: i64 = n / 2;
    let wb: i64 = 2 * wa;
    proof {
        let wai = wa as int;
        let wbi = wb as int;
        let ni = n as int;
        // Establish witness a=wa, b=wb
        assert(1 <= wai);
        assert(wai < ni);
        assert(wai < wbi);
        assert(wbi <= ni);
        // Show Gcd(wa, wb) == wa
        assert(wbi % wai == 0);
        assert(Gcd(wbi, wai) == wai);
        assert(wai % wbi == wai);
        assert(wai % wbi != 0);
        assert(Gcd(wai, wbi) == Gcd(wbi, wai % wbi));
        assert(Gcd(wai, wbi) == Gcd(wbi, wai));
        assert(Gcd(wai, wbi) == wai);
        assert(result as int == ni / 2);
        assert(wai == result as int);
        // Upper bound: for all valid (a, b), Gcd(a, b) * 2 <= b <= n, so Gcd(a, b) <= n/2 == result
        assert forall|a: int, b: int| (1 <= a && a < ni && a < b && b <= ni) implies #[trigger] Gcd(a, b) <= result as int by {
            GcdBound(a, b);
            assert(Gcd(a, b) * 2 <= b);
            assert(b <= ni);
            assert(Gcd(a, b) * 2 <= ni);
        };
    }
    result
}

fn main() {}

} // verus!
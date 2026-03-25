use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;

verus! {

spec fn MeetAt(x: int, y: int, a: int, b: int, t: int) -> bool {
    t >= 1 && x + t * a == y - t * b
}

fn TwoRabbits(x: i64, y: i64, a: i64, b: i64) -> (t: i64)
    requires
        x < y,
        a >= 1,
        b >= 1,
        a as int + b as int <= i64::MAX as int,
        y as int - x as int <= i64::MAX as int,
    ensures
        t == -1 || t >= 1,
        t >= 1 ==> MeetAt(x as int, y as int, a as int, b as int, t as int),
        t == -1 ==> forall|t_prime: int| t_prime >= 1 ==> !MeetAt(x as int, y as int, a as int, b as int, t_prime),
{
    let z = y - x;
    let c = a + b;
    if z % c != 0 {
        proof {
            let za: int = z as int;
            let ca: int = c as int;
            assert forall|t_prime: int| t_prime >= 1 implies
                !MeetAt(x as int, y as int, a as int, b as int, t_prime) by
            {
                if MeetAt(x as int, y as int, a as int, b as int, t_prime) {
                    let xa: int = x as int;
                    let ya: int = y as int;
                    let aa: int = a as int;
                    let ba: int = b as int;
                    assert(xa + t_prime * aa == ya - t_prime * ba);
                    assert(t_prime * aa + t_prime * ba == ya - xa);
                    assert(t_prime * (aa + ba) == ya - xa) by(nonlinear_arith)
                        requires t_prime * aa + t_prime * ba == ya - xa;
                    assert(t_prime * ca == za);
                    lemma_fundamental_div_mod(za, ca);
                    let q: int = za / ca;
                    let r: int = za % ca;
                    assert(za == ca * q + r);
                    assert(r > 0);
                    assert(r < ca);
                    assert(t_prime * ca == ca * q + r);
                    assert((t_prime - q) * ca == r) by(nonlinear_arith)
                        requires t_prime * ca == ca * q + r;
                    if t_prime == q {
                        assert(r == 0);
                    } else if t_prime > q {
                        assert(t_prime - q >= 1);
                        assert((t_prime - q) * ca >= ca) by(nonlinear_arith)
                            requires t_prime - q >= 1, ca >= 2;
                        assert(r >= ca);
                    } else {
                        assert(t_prime - q <= -1);
                        assert((t_prime - q) * ca <= -ca) by(nonlinear_arith)
                            requires t_prime - q <= -1, ca >= 2;
                        assert(r <= -ca);
                    }
                }
            };
        }
        -1i64
    } else {
        let t = z / c;
        proof {
            let za: int = z as int;
            let ca: int = c as int;
            let ta: int = t as int;
            lemma_fundamental_div_mod(za, ca);
            assert(za % ca == 0);
            assert(za == ca * ta + za % ca);
            assert(ca * ta == za);
            assert(ta * ca == za) by(nonlinear_arith)
                requires ca * ta == za;
            assert(ta >= 1) by(nonlinear_arith)
                requires ta * ca == za, za >= 1, ca >= 2;
            assert(ta * (a as int) + ta * (b as int) == (y as int) - (x as int)) by(nonlinear_arith)
                requires ta * ca == za, ca == (a as int) + (b as int), za == (y as int) - (x as int);
            assert((x as int) + ta * (a as int) == (y as int) - ta * (b as int));
        }
        t
    }
}

fn main() {}

} // verus!
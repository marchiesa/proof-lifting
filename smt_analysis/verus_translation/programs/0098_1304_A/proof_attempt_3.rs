use vstd::prelude::*;

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
            assert forall|t_prime: int| t_prime >= 1 implies !MeetAt(x as int, y as int, a as int, b as int, t_prime) by {
                if MeetAt(x as int, y as int, a as int, b as int, t_prime) {
                    assert(x as int + t_prime * (a as int) == y as int - t_prime * (b as int));
                    assert(t_prime * (a as int) + t_prime * (b as int) == y as int - x as int);
                    assert(t_prime * (a as int) + t_prime * (b as int) == t_prime * (a as int + b as int)) by (nonlinear_arith);
                    assert(t_prime * (c as int) == z as int);
                    assert((z as int) % (c as int) == 0) by (nonlinear_arith)
                        requires
                            t_prime * (c as int) == z as int,
                            c as int >= 2,
                        ;
                }
            };
        }
        -1i64
    } else {
        let t = z / c;
        proof {
            assert((t as int) * (c as int) == z as int);
            assert(t as int >= 1) by (nonlinear_arith)
                requires
                    (t as int) * (c as int) == z as int,
                    z as int >= 1,
                    c as int >= 2,
                ;
            assert((t as int) * (a as int) + (t as int) * (b as int) == (t as int) * (a as int + b as int)) by (nonlinear_arith);
            assert((t as int) * (a as int + b as int) == y as int - x as int);
            assert(x as int + (t as int) * (a as int) == y as int - (t as int) * (b as int));
        }
        t
    }
}

fn main() {}

} // verus!
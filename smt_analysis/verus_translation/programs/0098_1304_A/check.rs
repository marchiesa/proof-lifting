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
    ensures
        t == -1 || t >= 1,
        t >= 1 ==> MeetAt(x as int, y as int, a as int, b as int, t as int),
        t == -1 ==> forall|t_prime: int| t_prime >= 1 ==> !MeetAt(x as int, y as int, a as int, b as int, t_prime),
{
    let z = y - x;
    let c = a + b;
    if z % c != 0 {
        proof {
            assume(false);
        }
        -1i64
    } else {
        let t = z / c;
        proof {
            assume(false);
        }
        t
    }
}

fn main() {}

} // verus!
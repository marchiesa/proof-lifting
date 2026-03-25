use vstd::prelude::*;

verus! {

spec fn valid_pair(a: int, b: int, x: int) -> bool {
    1 <= a <= x &&
    1 <= b <= x &&
    a % b == 0 &&
    a * b > x &&
    a / b < x
}

spec fn solution_exists(x: int) -> bool {
    exists|a: int, b: int| valid_pair(a, b, x)
}

#[verifier::loop_isolation(false)]
fn ehab_construction(x: i64) -> (result: (i64, i64, bool))
    ensures
        result.2 ==> valid_pair(result.0 as int, result.1 as int, x as int),
        !result.2 ==> !solution_exists(x as int),
{
    let mut a: i64 = 0;
    let mut b: i64 = 0;
    let mut found: bool = false;

    let mut ai: i64 = 1;
    while ai <= x && !found
        invariant
            1 <= ai,
            found ==> valid_pair(a as int, b as int, x as int),
            !found ==> forall|a2: int, b2: int|
                1 <= a2 < ai as int && 1 <= b2 <= x as int
                    ==> !valid_pair(a2, b2, x as int),
        decreases x - ai,
    {
        let mut bi: i64 = 1;
        while bi <= ai && !found
            invariant
                1 <= ai <= x,
                1 <= bi,
                found ==> valid_pair(a as int, b as int, x as int),
                !found ==> forall|a2: int, b2: int|
                    1 <= a2 < ai as int && 1 <= b2 <= x as int
                        ==> !valid_pair(a2, b2, x as int),
                !found ==> forall|b2: int|
                    1 <= b2 < bi as int ==> !valid_pair(ai as int, b2, x as int),
            decreases ai - bi,
        {
            if ai % bi == 0 && ai * bi > x && ai / bi < x {
                a = ai;
                b = bi;
                found = true;
            }
            bi = bi + 1;
        }
        if !found {
            proof {
                assert forall|b2: int| ai as int < b2 <= x as int
                    implies !valid_pair(ai as int, b2, x as int) by
                {
                    assert(ai as int % b2 == ai as int);
                }
            }
        }
        ai = ai + 1;
    }
    (a, b, found)
}

fn main() {}

} // verus!
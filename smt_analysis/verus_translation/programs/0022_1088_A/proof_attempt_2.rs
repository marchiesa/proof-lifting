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
    requires 1 <= x
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
            !found ==> forall|a_: int, b_: int| 1 <= a_ < ai as int && 1 <= b_ <= x as int ==> !valid_pair(a_, b_, x as int),
        decreases x as int - ai as int
    {
        let mut bi: i64 = 1;
        while bi <= ai && !found
            invariant
                1 <= bi,
                1 <= ai <= x,
                found ==> valid_pair(a as int, b as int, x as int),
                !found ==> forall|a_: int, b_: int| 1 <= a_ < ai as int && 1 <= b_ <= x as int ==> !valid_pair(a_, b_, x as int),
                !found ==> forall|b_: int| 1 <= b_ < bi as int ==> !valid_pair(ai as int, b_, x as int),
            decreases ai as int - bi as int
        {
            if ai % bi == 0 && (ai as i128) * (bi as i128) > (x as i128) && ai / bi < x {
                a = ai;
                b = bi;
                found = true;
            }
            bi = bi + 1;
        }
        if !found {
            assert forall|b_: int| ai as int < b_ <= x as int implies !valid_pair(ai as int, b_, x as int) by {
                assert(ai as int % b_ == ai as int) by (nonlinear_arith);
            }
        }
        ai = ai + 1;
    }
    (a, b, found)
}

fn main() {}

} // verus!
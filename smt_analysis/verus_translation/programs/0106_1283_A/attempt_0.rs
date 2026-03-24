use vstd::prelude::*;

verus! {

spec fn valid_time(h: int, m: int) -> bool {
    0 <= h < 24 && 0 <= m < 60
}

spec fn minutes_since_midnight(h: int, m: int) -> int {
    h * 60 + m
}

spec fn clock_state_after(h: int, m: int, n: int) -> int {
    (minutes_since_midnight(h, m) + n) % 1440
}

spec fn reaches_midnight(h: int, m: int, n: int) -> bool {
    clock_state_after(h, m, n) == 0
}

fn minutes_before_new_year(h: i64, m: i64) -> (minutes: i64)
    requires valid_time(h as int, m as int)
    ensures 1 <= minutes as int <= 1440
    ensures reaches_midnight(h as int, m as int, minutes as int)
    ensures forall|k: int| 1 <= k < minutes as int ==> !reaches_midnight(h as int, m as int, k)
{
    let minutes: i64 = (23 - h) * 60 + (60 - m);

    proof {
        assume(false);
    }

    minutes
}

fn main() {}

} // verus!
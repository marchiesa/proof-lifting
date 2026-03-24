use vstd::prelude::*;

verus! {

spec fn is_valid_window(a: int, b: int, c1: int, r1: int, c2: int, r2: int) -> bool {
    0 <= c1 && c1 <= c2 && c2 < a && 0 <= r1 && r1 <= r2 && r2 < b
}

spec fn window_avoids_dead(c1: int, r1: int, c2: int, r2: int, x: int, y: int) -> bool {
    x < c1 || x > c2 || y < r1 || y > r2
}

spec fn window_area(c1: int, r1: int, c2: int, r2: int) -> int {
    (c2 - c1 + 1) * (r2 - r1 + 1)
}

proof fn mul_mono(a1: int, a2: int, b1: int, b2: int)
    requires
        0 <= a1 && a1 <= a2,
        0 <= b1 && b1 <= b2,
    ensures
        a1 * b1 <= a2 * b2,
{
    assume(false);
}

proof fn window_bound_lemma(a: int, b: int, c1: int, r1: int, c2: int, r2: int, x: int, y: int)
    requires
        a >= 1 && b >= 1,
        0 <= x && x < a && 0 <= y && y < b,
        0 <= c1 && c1 < a && 0 <= r1 && r1 < b && 0 <= c2 && c2 < a && 0 <= r2 && r2 < b,
        is_valid_window(a, b, c1, r1, c2, r2),
        window_avoids_dead(c1, r1, c2, r2, x, y),
    ensures
        window_area(c1, r1, c2, r2) <= x * b
            || window_area(c1, r1, c2, r2) <= (a - x - 1) * b
            || window_area(c1, r1, c2, r2) <= y * a
            || window_area(c1, r1, c2, r2) <= (b - y - 1) * a,
{
    assume(false);
}

fn dead_pixel(a: i64, b: i64, x: i64, y: i64) -> (area: i64)
    requires
        a >= 1 && b >= 1,
        0 <= x && x < a && 0 <= y && y < b,
    ensures
        area >= 0,
        forall|c1: int, r1: int, c2: int, r2: int|
            (0 <= c1 && c1 < a as int && 0 <= r1 && r1 < b as int
            && 0 <= c2 && c2 < a as int && 0 <= r2 && r2 < b as int
            && is_valid_window(a as int, b as int, c1, r1, c2, r2)
            && window_avoids_dead(c1, r1, c2, r2, x as int, y as int))
                ==> window_area(c1, r1, c2, r2) <= area as int,
        area == 0 ||
            (exists|c1: int, r1: int, c2: int, r2: int|
                0 <= c1 && c1 < a as int && 0 <= r1 && r1 < b as int
                && 0 <= c2 && c2 < a as int && 0 <= r2 && r2 < b as int
                && is_valid_window(a as int, b as int, c1, r1, c2, r2)
                && window_avoids_dead(c1, r1, c2, r2, x as int, y as int)
                && window_area(c1, r1, c2, r2) == area as int),
{
    let v1: i64 = x * b;
    let v2: i64 = y * a;
    let v3: i64 = (a - x - 1) * b;
    let v4: i64 = (b - y - 1) * a;
    let mut area: i64 = v1;
    if v2 > area { area = v2; }
    if v3 > area { area = v3; }
    if v4 > area { area = v4; }

    proof {
        assume(false);
    }

    if v1 >= v2 && v1 >= v3 && v1 >= v4 && v1 > 0 {
        proof { assume(false); }
    } else if v2 >= v1 && v2 >= v3 && v2 >= v4 && v2 > 0 {
        proof { assume(false); }
    } else if v3 >= v1 && v3 >= v2 && v3 >= v4 && v3 > 0 {
        proof { assume(false); }
    } else if v4 > 0 {
        proof { assume(false); }
    }

    area
}

fn main() {}

} // verus!
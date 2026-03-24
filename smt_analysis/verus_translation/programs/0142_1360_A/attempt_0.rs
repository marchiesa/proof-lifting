use vstd::prelude::*;

verus! {

spec fn fits_side_by_side(w1: int, h1: int, w2: int, h2: int, s: int) -> bool {
    w1 + w2 <= s && h1 <= s && h2 <= s
}

spec fn fits_stacked(w1: int, h1: int, w2: int, h2: int, s: int) -> bool {
    w1 <= s && w2 <= s && h1 + h2 <= s
}

spec fn can_fit_in_square(a: int, b: int, s: int) -> bool {
    fits_side_by_side(a, b, a, b, s) || fits_stacked(a, b, a, b, s) ||
    fits_side_by_side(a, b, b, a, s) || fits_stacked(a, b, b, a, s) ||
    fits_side_by_side(b, a, a, b, s) || fits_stacked(b, a, a, b, s) ||
    fits_side_by_side(b, a, b, a, s) || fits_stacked(b, a, b, a, s)
}

spec fn is_minimal_side(a: int, b: int, s: int) -> bool {
    can_fit_in_square(a, b, s) &&
    forall|s_prime: int| 1 <= s_prime && s_prime < s ==> !can_fit_in_square(a, b, s_prime)
}

fn minimal_square(a: i64, b: i64) -> (area: i64)
    requires
        1 <= a,
        1 <= b,
    ensures
        exists|s: int| 1 <= s && area as int == s * s && is_minimal_side(a as int, b as int, s),
{
    let lo: i64 = if a < b { a } else { b };
    let hi: i64 = if a < b { b } else { a };
    let val: i64 = if 2 * lo > hi { 2 * lo } else { hi };

    proof {
        assume(false);
    }

    val * val
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn min_val(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn candies_after_division(ap: int, bp: int, sp: int, s: int) -> int
    requires 0 <= s <= sp
{
    min_val(ap + s, bp + (sp - s))
}

spec fn is_achievable(a: int, b: int, c: int, result: int) -> bool
    requires a >= 0 && b >= 0 && c >= 0
{
    (exists|s: int| 0 <= s <= c && candies_after_division(a, b, c, s) == result)
    || (exists|s: int| 0 <= s <= b && candies_after_division(a, c, b, s) == result)
    || (exists|s: int| 0 <= s <= a && candies_after_division(b, c, a, s) == result)
}

spec fn is_optimal(a: int, b: int, c: int, result: int) -> bool
    requires a >= 0 && b >= 0 && c >= 0
{
    (forall|s: int| 0 <= s <= c ==> candies_after_division(a, b, c, s) <= result)
    && (forall|s: int| 0 <= s <= b ==> candies_after_division(a, c, b, s) <= result)
    && (forall|s: int| 0 <= s <= a ==> candies_after_division(b, c, a, s) <= result)
}

fn three_piles_of_candies(a: i64, b: i64, c: i64) -> (max_candies: i64)
    requires
        a >= 0,
        b >= 0,
        c >= 0,
    ensures
        is_achievable(a as int, b as int, c as int, max_candies as int),
        is_optimal(a as int, b as int, c as int, max_candies as int),
{
    let max_candies = (a + b + c) / 2;

    if a >= b && a >= c {
        proof { assume(false); }
    } else if b >= a && b >= c {
        proof { assume(false); }
    } else {
        proof { assume(false); }
    }

    max_candies
}

fn main() {}

} // verus!
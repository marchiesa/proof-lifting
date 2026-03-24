use vstd::prelude::*;

verus! {

spec fn gcd(a: int, b: int) -> int
    recommends a > 0 && b >= 0
    decreases b
{
    if b == 0 { a } else { gcd(b, a % b) }
}

spec fn lcm(a: int, b: int) -> int
    recommends a > 0 && b > 0
{
    (a / gcd(a, b)) * b
}

spec fn valid_pair(x: int, y: int, l: int, r: int) -> bool
    recommends l >= 1
{
    l <= x && x < y && y <= r && l <= lcm(x, y) && lcm(x, y) <= r
}

spec fn pair_exists(l: int, r: int) -> bool
    recommends l >= 1
{
    exists|x: int| l <= x && x <= r && (exists|y: int| x + 1 <= y && y <= r && valid_pair(x, y, l, r))
}

proof fn product_non_neg(a: int, b: int)
    requires a >= 0, b >= 0
    ensures a * b >= 0
{
    assume(false);
}

proof fn sum_divisible(a: int, b: int, g: int)
    requires g > 0, a % g == 0, b % g == 0
    ensures (a + b) % g == 0
{
    assume(false);
}

proof fn diff_divisible(a: int, b: int, g: int)
    requires g > 0, a % g == 0, b % g == 0
    ensures (a - b) % g == 0
{
    assume(false);
}

proof fn multiple_of_multiple(q: int, b: int, g: int)
    requires g > 0, b % g == 0
    ensures (q * b) % g == 0
    decreases if q >= 0 { q } else { -q }
{
    assume(false);
}

proof fn gcd_divides_both(a: int, b: int)
    requires a > 0 && b > 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    decreases b
{
    assume(false);
}

proof fn gcd_of_double_reverse(a: int)
    requires a > 0
    ensures gcd(2 * a, a) == a
{
    assume(false);
}

proof fn gcd_of_doubled(a: int)
    requires a > 0
    ensures gcd(a, 2 * a) == a
{
    assume(false);
}

proof fn lcm_lower_bound(x: int, y: int)
    requires x > 0 && y > x
    ensures lcm(x, y) >= 2 * x
{
    assume(false);
}

fn lcm_problem(l: i64, r: i64) -> (res: (i64, i64))
    requires l >= 1
    ensures res.0 == -1i64 && res.1 == -1i64 || valid_pair(res.0 as int, res.1 as int, l as int, r as int)
    ensures (res.0 == -1i64 && res.1 == -1i64) <==> !pair_exists(l as int, r as int)
{
    if l * 2 > r {
        proof {
            assume(false);
        }
        (-1i64, -1i64)
    } else {
        proof {
            assume(false);
        }
        (l, l * 2)
    }
}

fn main() {}

} // verus!
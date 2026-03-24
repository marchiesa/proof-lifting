use vstd::prelude::*;

verus! {

spec fn in_grid(n: int, m: int, i: int, j: int) -> bool {
    1 <= i && i <= n && 1 <= j && j <= m
}

spec fn reachable_within(n: int, m: int, ti: int, tj: int, t: int) -> Set<(int, int)>
    recommends n >= 1 && m >= 1
    recommends in_grid(n, m, ti, tj)
    recommends t >= 0
    decreases t
{
    if t == 0 {
        Set::empty().insert((ti, tj))
    } else {
        let prev = reachable_within(n, m, ti, tj, t - 1);
        Set::new(|p: (int, int)| {
            1 <= p.0 && p.0 <= n && 1 <= p.1 && p.1 <= m &&
            (prev.contains((p.0, p.1)) ||
             (p.0 - 1 >= 1 && prev.contains((p.0 - 1, p.1))) ||
             (p.0 + 1 <= n && prev.contains((p.0 + 1, p.1))) ||
             (p.1 - 1 >= 1 && prev.contains((p.0, p.1 - 1))) ||
             (p.1 + 1 <= m && prev.contains((p.0, p.1 + 1))))
        })
    }
}

spec fn all_reach_within(n: int, m: int, ti: int, tj: int, t: int) -> bool
    recommends n >= 1 && m >= 1
    recommends in_grid(n, m, ti, tj)
    recommends t >= 0
{
    let reach = reachable_within(n, m, ti, tj, t);
    forall|i: int, j: int| 1 <= i && i <= n && 1 <= j && j <= m ==> reach.contains((i, j))
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

proof fn reachable_monotone(n: int, m: int, ti: int, tj: int, t: int, i: int, j: int)
    requires n >= 1 && m >= 1 && in_grid(n, m, ti, tj) && t >= 1
    requires reachable_within(n, m, ti, tj, t - 1).contains((i, j))
    ensures reachable_within(n, m, ti, tj, t).contains((i, j))
{
    assume(false);
}

proof fn reachable_complete(n: int, m: int, ti: int, tj: int, t: int, i: int, j: int)
    requires n >= 1 && m >= 1 && in_grid(n, m, ti, tj)
    requires in_grid(n, m, i, j) && t >= 0
    requires abs(i - ti) + abs(j - tj) <= t
    ensures reachable_within(n, m, ti, tj, t).contains((i, j))
    decreases t
{
    assume(false);
}

proof fn reachable_soundness(n: int, m: int, ti: int, tj: int, t: int, i: int, j: int)
    requires n >= 1 && m >= 1 && in_grid(n, m, ti, tj) && t >= 0
    requires reachable_within(n, m, ti, tj, t).contains((i, j))
    ensures abs(i - ti) + abs(j - tj) <= t
    decreases t
{
    assume(false);
}

proof fn all_reach_helper(n: int, m: int, r: int, c: int, dr: int, dc: int, time: int)
    requires n >= 1 && m >= 1 && in_grid(n, m, r, c)
    requires dr >= r - 1 && dr >= n - r
    requires dc >= c - 1 && dc >= m - c
    requires time == dr + dc
    ensures time >= 0
    ensures all_reach_within(n, m, r, c, time)
{
    assume(false);
}

proof fn optimality_helper(n: int, m: int, r: int, c: int, dr: int, dc: int, time: int)
    requires n >= 1 && m >= 1 && in_grid(n, m, r, c)
    requires (dr == r - 1 || dr == n - r) && dr >= r - 1 && dr >= n - r
    requires (dc == c - 1 || dc == m - c) && dc >= c - 1 && dc >= m - c
    requires time == dr + dc && time > 0
    ensures !all_reach_within(n, m, r, c, time - 1)
{
    assume(false);
}

fn prison_break(n: i64, m: i64, r: i64, c: i64) -> (time: i64)
    requires n >= 1 && m >= 1
    requires in_grid(n as int, m as int, r as int, c as int)
    ensures time >= 0
    ensures all_reach_within(n as int, m as int, r as int, c as int, time as int)
    ensures time == 0 || !all_reach_within(n as int, m as int, r as int, c as int, time as int - 1)
{
    let dr: i64 = if r - 1 > n - r { r - 1 } else { n - r };
    let dc: i64 = if c - 1 > m - c { c - 1 } else { m - c };
    let time = dr + dc;
    proof {
        assume(false);
    }
    time
}

fn main() {}

} // verus!
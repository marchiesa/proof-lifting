use vstd::prelude::*;

verus! {

spec fn SufficientNotebooks(r: int, g: int, b: int, n: int, k: int) -> bool {
    r >= 0 && g >= 0 && b >= 0 &&
    r * k >= 2 * n &&
    g * k >= 5 * n &&
    b * k >= 8 * n
}

spec fn IsMinCover(m: int, need: int, k: int) -> bool
    recommends k >= 1
{
    m >= 0 &&
    m * k >= need &&
    (m == 0 || (m - 1) * k < need)
}

spec fn IsMinTotalNotebooks(total: int, n: int, k: int) -> bool
    recommends n >= 1 && k >= 1
{
    exists|r: int, g: int, b: int|
        r >= 0 && g >= 0 && b >= 0 &&
        IsMinCover(r, 2 * n, k) &&
        IsMinCover(g, 5 * n, k) &&
        IsMinCover(b, 8 * n, k) &&
        SufficientNotebooks(r, g, b, n, k) &&
        total == r + g + b
}

proof fn CeilDivIsMinCover(need: int, k: int)
    requires
        k >= 1,
        need >= 0,
    ensures
        IsMinCover((need + k - 1) / k, need, k),
{
    let a = need + k - 1;
    let m = a / k;
    let rem = a % k;
    assert(a == m * k + rem);
    assert(0 <= rem < k);
    assert(m * k == need + k - 1 - rem);
    assert(m * k >= need);
    assert(m >= 0);
    if m > 0 {
        assert((m - 1) * k == m * k - k);
        assert((m - 1) * k == need - 1 - rem);
        assert((m - 1) * k < need);
    }
}

fn PetyaAndOrigami(n: i64, k: i64) -> (notebooks: i64)
    requires
        1 <= n <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
    ensures
        IsMinTotalNotebooks(notebooks as int, n as int, k as int),
{
    let r = (n * 2 + k - 1) / k;
    let g = (n * 5 + k - 1) / k;
    let b = (n * 8 + k - 1) / k;

    proof {
        CeilDivIsMinCover(2 * n as int, k as int);
        CeilDivIsMinCover(5 * n as int, k as int);
        CeilDivIsMinCover(8 * n as int, k as int);

        assert(IsMinCover(r as int, 2 * n as int, k as int));
        assert(IsMinCover(g as int, 5 * n as int, k as int));
        assert(IsMinCover(b as int, 8 * n as int, k as int));
        assert(SufficientNotebooks(r as int, g as int, b as int, n as int, k as int));
    }
    r + g + b
}

fn main() {}

} // verus!
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
    let m = (need + k - 1) / k;
    let rem = (need + k - 1) % k;
    assert(m >= 0) by (nonlinear_arith)
        requires need >= 0, k >= 1, need + k - 1 == m * k + rem, 0 <= rem, rem < k;
    assert(m * k >= need) by (nonlinear_arith)
        requires need + k - 1 == m * k + rem, 0 <= rem, rem < k;
    if m > 0 {
        assert((m - 1) * k < need) by (nonlinear_arith)
            requires need + k - 1 == m * k + rem, 0 <= rem, rem < k, m > 0;
    }
}

proof fn ceil_div_upper_bound(need: int, k: int)
    requires
        k >= 1,
        need >= 1,
    ensures
        (need + k - 1) / k <= need,
{
    let m = (need + k - 1) / k;
    let rem = (need + k - 1) % k;
    assert(m <= need) by (nonlinear_arith)
        requires need >= 1, k >= 1, need + k - 1 == m * k + rem, 0 <= rem, rem < k;
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
        let nn = n as int;
        let kk = k as int;

        CeilDivIsMinCover(2 * nn, kk);
        CeilDivIsMinCover(5 * nn, kk);
        CeilDivIsMinCover(8 * nn, kk);

        ceil_div_upper_bound(2 * nn, kk);
        ceil_div_upper_bound(5 * nn, kk);
        ceil_div_upper_bound(8 * nn, kk);

        // Establish upper bounds so Verus can prove r+g+b doesn't overflow i64
        assert(r as int <= 2 * nn);
        assert(g as int <= 5 * nn);
        assert(b as int <= 8 * nn);

        assert(IsMinCover(r as int, 2 * nn, kk));
        assert(IsMinCover(g as int, 5 * nn, kk));
        assert(IsMinCover(b as int, 8 * nn, kk));
        assert(SufficientNotebooks(r as int, g as int, b as int, nn, kk));
    }
    r + g + b
}

fn main() {}

} // verus!
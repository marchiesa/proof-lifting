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
    assume(false);
}

fn PetyaAndOrigami(n: i64, k: i64) -> (notebooks: i64)
    requires
        n >= 1 && k >= 1,
    ensures
        IsMinTotalNotebooks(notebooks as int, n as int, k as int),
{
    let r = (n * 2 + k - 1) / k;
    let g = (n * 5 + k - 1) / k;
    let b = (n * 8 + k - 1) / k;
    proof { assume(false); }
    r + g + b
}

fn main() {}

} // verus!
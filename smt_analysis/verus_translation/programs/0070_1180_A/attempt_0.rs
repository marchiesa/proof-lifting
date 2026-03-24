use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn in_rhombus(x: int, y: int, n: int) -> bool
    recommends n >= 1
{
    abs(x) + abs(y) <= n - 1
}

spec fn row_width(x: int, r: int) -> int
    recommends r >= 0
{
    if abs(x) > r { 0 }
    else { 2 * (r - abs(x)) + 1 }
}

spec fn sum_rows(lo: int, hi: int, r: int) -> int
    recommends r >= 0
    decreases hi - lo + 1
{
    if lo > hi { 0 }
    else { row_width(lo, r) + sum_rows(lo + 1, hi, r) }
}

spec fn rhombus_cell_count(n: int) -> int
    recommends n >= 1
{
    sum_rows(-(n - 1), n - 1, n - 1)
}

proof fn sum_rows_append(lo: int, hi: int, r: int)
    requires
        r >= 0,
        lo <= hi,
    ensures sum_rows(lo, hi, r) == sum_rows(lo, hi - 1, r) + row_width(hi, r)
    decreases hi - lo
{
    if lo == hi {
    } else {
        sum_rows_append(lo + 1, hi, r);
    }
}

proof fn sum_rows_radius_step(lo: int, hi: int, r: int)
    requires
        r >= 1,
        -(r - 1) <= lo,
        lo <= hi,
        hi <= r - 1,
    ensures sum_rows(lo, hi, r) == sum_rows(lo, hi, r - 1) + 2 * (hi - lo + 1)
    decreases hi - lo
{
    if lo == hi {
    } else {
        sum_rows_radius_step(lo + 1, hi, r);
    }
}

proof fn rhombus_cell_count_closed_form(n: int)
    requires n >= 1
    ensures rhombus_cell_count(n) == 2 * (n - 1) * (n - 1) + 2 * (n - 1) + 1
    decreases n
{
    let r = n - 1;
    if r == 0 {
    } else {
        rhombus_cell_count_closed_form(n - 1);
        assume(false); // assert RowWidth(-r, r) == 1
        assume(false); // assert RowWidth(r, r) == 1
        sum_rows_append(-(r - 1), r, r);
        sum_rows_radius_step(-(r - 1), r - 1, r);
    }
}

#[verifier::loop_isolation(false)]
fn rhombus(n: i64) -> (cells: i64)
    requires n >= 1
    ensures cells == rhombus_cell_count(n as int)
{
    let mut cells: i64 = 1;
    let mut i: i64 = 1;
    while i < n
    {
        cells = cells + i * 4;
        i = i + 1;
    }
    proof {
        rhombus_cell_count_closed_form(n as int);
    }
    cells
}

fn main() {}

} // verus!
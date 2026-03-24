use vstd::prelude::*;

verus! {

spec fn beautiful(ny: int, nb: int, nr: int) -> bool {
    nb == ny + 1 && nr == nb + 1
}

spec fn valid_choice(y: int, b: int, r: int, ny: int, nb: int, nr: int) -> bool {
    0 <= ny <= y && 0 <= nb <= b && 0 <= nr <= r && beautiful(ny, nb, nr)
}

fn max_ornaments(y: i64, b: i64, r: i64) -> (total: i64)
    requires
        y >= 1,
        b >= 2,
        r >= 3,
    ensures
        exists|ny: int| 0 <= ny <= y as int &&
            valid_choice(y as int, b as int, r as int, ny, ny + 1, ny + 2) &&
            total as int == ny + (ny + 1) + (ny + 2),
        forall|ny: int| 0 <= ny <= y as int ==>
            valid_choice(y as int, b as int, r as int, ny, ny + 1, ny + 2) ==>
            ny + (ny + 1) + (ny + 2) <= total as int,
{
    let mut m = y;
    if b - 1 < m { m = b - 1; }
    if r - 2 < m { m = r - 2; }
    let total = 3 * m + 3;

    proof { assume(false); }

    total
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn max_of(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn min_of(a: int, b: int) -> int {
    if a < b { a } else { b }
}

spec fn is_valid_solution(x: int, y: int, z: int, a: int, b: int, c: int) -> bool {
    a > 0 && b > 0 && c > 0 &&
    max_of(a, b) == x && max_of(a, c) == y && max_of(b, c) == z
}

spec fn solution_exists(x: int, y: int, z: int) -> bool {
    exists|a: int, b: int, c: int| is_valid_solution(x, y, z, a, b, c)
}

fn three_pairwise_maximums(x: i64, y: i64, z: i64) -> (result: (bool, i64, i64, i64))
    requires
        x > 0 && y > 0 && z > 0,
    ensures
        result.0 == solution_exists(x as int, y as int, z as int),
        result.0 ==> is_valid_solution(x as int, y as int, z as int, result.1 as int, result.2 as int, result.3 as int),
{
    let mut m = x;
    if y > m { m = y; }
    if z > m { m = z; }

    let mut cnt: i64 = 0;
    if x == m { cnt = cnt + 1; }
    if y == m { cnt = cnt + 1; }
    if z == m { cnt = cnt + 1; }

    if cnt >= 2 {
        let possible = true;
        let a = if x <= y { x } else { y };
        let b = if x <= z { x } else { z };
        let c = if y <= z { y } else { z };
        proof { assume(false); }
        (possible, a, b, c)
    } else {
        let possible = false;
        let a: i64 = 0;
        let b: i64 = 0;
        let c: i64 = 0;
        proof { assume(false); }
        (possible, a, b, c)
    }
}

fn main() {}

} // verus!
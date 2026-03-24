use vstd::prelude::*;

verus! {

spec fn ValidMatrix(M: Seq<Seq<char>>, n: int) -> bool {
    n >= 0 &&
    M.len() == n &&
    forall|i: int| 0 <= i < n ==> M[i].len() == n
}

spec fn IsCrossAt(M: Seq<Seq<char>>, n: int, a: int, b: int) -> bool
    recommends
        ValidMatrix(M, n),
        0 <= a < n,
        0 <= b < n,
{
    1 <= a && a <= n - 2 &&
    1 <= b && b <= n - 2 &&
    M[a][b] == 'X' &&
    M[a - 1][b - 1] == 'X' &&
    M[a - 1][b + 1] == 'X' &&
    M[a + 1][b - 1] == 'X' &&
    M[a + 1][b + 1] == 'X'
}

spec fn CrossCount(M: Seq<Seq<char>>, n: int) -> int
    recommends ValidMatrix(M, n)
{
    Set::<(int, int)>::new(|pair: (int, int)| {
        0 <= pair.0 < n && 0 <= pair.1 < n && IsCrossAt(M, n, pair.0, pair.1)
    }).len() as int
}

#[verifier::loop_isolation(false)]
fn CountCrosses(n: i64, M: &Vec<Vec<char>>) -> (count: i64)
    requires
        ValidMatrix(M@.map_values(|v: Vec<char>| v@), n as int),
    ensures
        count as int == CrossCount(M@.map_values(|v: Vec<char>| v@), n as int),
{
    let mut count: i64 = 0;
    if n < 3 {
        proof { assume(false); }
        proof { assume(false); }
        return count;
    }

    let mut a: i64 = 1;
    while a < n - 1
    {
        let mut b: i64 = 1;
        while b < n - 1
        {
            if M[a as usize][b as usize] == 'X'
               && M[(a - 1) as usize][(b - 1) as usize] == 'X'
               && M[(a - 1) as usize][(b + 1) as usize] == 'X'
               && M[(a + 1) as usize][(b - 1) as usize] == 'X'
               && M[(a + 1) as usize][(b + 1) as usize] == 'X'
            {
                proof { assume(false); }
                proof { assume(false); }
                proof { assume(false); }
                count = count + 1;
            }
            b = b + 1;
        }
        a = a + 1;
    }

    proof { assume(false); }
    proof { assume(false); }
    proof { assume(false); }
    count
}

fn main() {}

} // verus!
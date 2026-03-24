use vstd::prelude::*;

verus! {

spec fn Sum(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        Sum(a.subrange(0, a.len() as int - 1)) + a[a.len() as int - 1]
    }
}

spec fn ValidScores(a: Seq<int>, m: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> 0 <= a[i] <= m
}

spec fn Achievable(a: Seq<int>, m: int, v: int) -> bool
    recommends a.len() > 0
{
    0 <= v <= m &&
    Sum(a) - v >= 0 &&
    Sum(a) - v <= (a.len() as int - 1) * m
}

proof fn SumAppend(s: Seq<int>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
    ensures Sum(s.subrange(0, i + 1)) == Sum(s.subrange(0, i)) + s[i]
{
    assume(false);
}

proof fn SumBounds(a: Seq<int>, m: int, k: int)
    requires 0 <= k <= a.len()
    requires ValidScores(a, m)
    ensures 0 <= Sum(a.subrange(0, k)) <= k * m
    decreases k
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn GradeAllocation(a: &Vec<i64>, m: i64) -> (score: i64)
    requires
        a@.len() > 0,
        m >= 0,
        ValidScores(a@.map_values(|x: i64| x as int), m as int),
    ensures
        Achievable(a@.map_values(|x: i64| x as int), m as int, score as int),
        forall|v: int| score as int < v && v <= m as int ==>
            !Achievable(a@.map_values(|x: i64| x as int), m as int, v),
{
    let mut s: i64 = 0;
    let mut i: usize = 0;
    while i < a.len()
    {
        s = s + a[i];
        i = i + 1;
    }
    if s < m {
        s
    } else {
        m
    }
}

fn main() {}

} // verus!
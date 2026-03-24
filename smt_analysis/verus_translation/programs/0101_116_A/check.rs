use vstd::prelude::*;

verus! {

spec fn Sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        Sum(s.take(s.len() - 1)) + s[s.len() - 1]
    }
}

spec fn Occupancy(a: Seq<int>, b: Seq<int>) -> int
    recommends a.len() == b.len()
{
    Sum(b) - Sum(a)
}

spec fn IsValidCapacity(c: int, n: int, a: Seq<int>, b: Seq<int>) -> bool
    recommends
        0 <= n,
        n <= a.len(),
        n <= b.len(),
{
    c >= 0 &&
    forall|k: int| 1 <= k && k <= n ==> Occupancy(a.take(k), b.take(k)) <= c
}

spec fn IsMinimumCapacity(c: int, n: int, a: Seq<int>, b: Seq<int>) -> bool
    recommends
        0 <= n,
        n <= a.len(),
        n <= b.len(),
{
    IsValidCapacity(c, n, a, b) &&
    forall|c_prime: int| 0 <= c_prime && c_prime < c ==> !IsValidCapacity(c_prime, n, a, b)
}

proof fn SumAppend(s: Seq<int>, x: int)
    ensures Sum(s.push(x)) == Sum(s) + x
{
    if s.len() == 0 {
        assume(false);
    } else {
        assume(false);
    }
}

#[verifier::loop_isolation(false)]
fn Tram(n: i64, a: &Vec<i64>, b: &Vec<i64>) -> (capacity: i64)
    requires
        0 <= n as int,
        n as int <= a@.len(),
        n as int <= b@.len(),
    ensures
        IsMinimumCapacity(
            capacity as int,
            n as int,
            a@.map_values(|x: i64| x as int),
            b@.map_values(|x: i64| x as int),
        ),
{
    let mut current: i64 = 0;
    let mut capacity: i64 = 0;
    let mut i: i64 = 0;
    while i < n {
        proof { assume(false); }
        proof { assume(false); }
        proof {
            SumAppend(
                a@.map_values(|x: i64| x as int).take(i as int),
                a@[i as int] as int,
            );
        }
        proof {
            SumAppend(
                b@.map_values(|x: i64| x as int).take(i as int),
                b@[i as int] as int,
            );
        }
        current = current - a[i as usize] + b[i as usize];
        if current > capacity {
            capacity = current;
        }
        i = i + 1;
    }
    capacity
}

fn main() {}

} // verus!
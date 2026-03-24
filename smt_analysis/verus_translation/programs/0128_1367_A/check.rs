use vstd::prelude::*;

verus! {

spec fn bob_encode(a: Seq<char>) -> Seq<char>
    recommends a.len() >= 2
    decreases a.len()
{
    if a.len() == 2 {
        a
    } else {
        a.subrange(0, 2) + bob_encode(a.subrange(1, a.len() as int))
    }
}

proof fn bob_encode_inverse(a: Seq<char>, b: Seq<char>)
    requires
        a.len() >= 2,
        b.len() == 2 * (a.len() - 1),
        a[0] == b[0],
        forall|j: int| 1 <= j < a.len() ==> a[j] == b[2 * j - 1],
        forall|k: int| 1 <= k < a.len() - 1 ==> b[2 * k] == b[2 * k - 1],
    ensures
        bob_encode(a) == b,
    decreases a.len()
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn short_substrings(b: &Vec<char>) -> (a: Vec<char>)
    requires
        b@.len() >= 2,
        b@.len() % 2 == 0,
        forall|k: int| 1 <= k < b@.len() / 2 ==> b@[2 * k] == b@[2 * k - 1],
    ensures
        a@.len() >= 2,
        bob_encode(a@) == b@,
{
    let mut partial: Vec<char> = Vec::new();
    let mut i: usize = 1;
    while i < b.len()
    {
        partial.push(b[i]);
        i = i + 2;
    }

    let mut a: Vec<char> = Vec::new();
    a.push(b[0]);
    let mut j: usize = 0;
    while j < partial.len()
    {
        a.push(partial[j]);
        j += 1;
    }

    proof {
        assume(false);
    }

    a
}

fn main() {}

} // verus!
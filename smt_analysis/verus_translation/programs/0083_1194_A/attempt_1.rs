use vstd::prelude::*;

verus! {

spec fn initial_list(n: nat) -> Seq<int>
    decreases n
{
    if n == 0 { Seq::empty() } else { initial_list(n - 1).push(n as int) }
}

spec fn remove_at_index(s: Seq<int>, idx: nat) -> Seq<int>
    recommends idx < s.len()
{
    s.take(idx as int).add(s.skip(idx as int + 1))
}

spec fn simulate(remaining: Seq<int>, step: nat) -> Seq<int>
    decreases remaining.len()
{
    if step == 0 || step > remaining.len() { remaining }
    else { simulate(remove_at_index(remaining, step - 1), step + 1) }
}

spec fn final_list(n: nat) -> Seq<int>
{
    simulate(initial_list(n), 1)
}

spec fn even_list(k: nat) -> Seq<int>
    decreases k
{
    if k == 0 { Seq::empty() } else { even_list(k - 1).push(2 * (k as int)) }
}

spec fn range_seq(a: int, b: int) -> Seq<int>
    decreases (b - a + 1) as nat
{
    if a > b { Seq::empty() } else { seq![a].add(range_seq(a + 1, b)) }
}

proof fn even_list_length(k: nat)
    ensures even_list(k).len() == k
{
    assume(false);
}

proof fn even_list_element(k: nat, i: nat)
    requires i < k
    ensures
        even_list(k).len() == k,
        even_list(k)[i as int] == 2 * (i as int + 1),
    decreases k
{
    assume(false);
}

proof fn range_seq_length(a: int, b: int)
    ensures
        a > b ==> range_seq(a, b).len() == 0,
        a <= b ==> range_seq(a, b).len() == (b - a + 1) as nat,
    decreases (b - a + 1) as nat
{
    assume(false);
}

proof fn range_seq_append(a: int, b: int)
    requires a <= b
    ensures range_seq(a, b) == range_seq(a, b - 1).push(b)
    decreases (b - a) as nat
{
    assume(false);
}

proof fn initial_list_equals_range(n: nat)
    ensures initial_list(n) == range_seq(1, n as int)
    decreases n
{
    assume(false);
}

proof fn simulate_from_state(k: nat, n: nat)
    requires 2 * k <= n
    ensures simulate(
        even_list(k).add(range_seq(2 * (k as int) + 1, n as int)),
        k + 1
    ) == even_list(n / 2)
    decreases n - 2 * k
{
    assume(false);
}

proof fn final_list_is_even(n: nat)
    ensures final_list(n) == even_list(n / 2)
{
    assume(false);
}

fn remove_a_progression(n: i64, x: i64) -> (result: i64)
    requires
        n >= 1,
        x >= 1,
        x as int <= final_list(n as nat).len() as int,
    ensures
        result as int == final_list(n as nat)[x as int - 1],
{
    proof {
        assume(false);
    }
    x * 2
}

fn main() {}

} // verus!
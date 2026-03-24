use vstd::prelude::*;

verus! {

spec fn initial_list(n: nat) -> Seq<int>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        initial_list((n - 1) as nat).push(n as int)
    }
}

spec fn remove_at_index(s: Seq<int>, idx: nat) -> Seq<int>
    recommends idx < s.len()
{
    s.subrange(0, idx as int) + s.subrange(idx as int + 1, s.len() as int)
}

spec fn simulate(remaining: Seq<int>, step: nat) -> Seq<int>
    decreases remaining.len()
{
    if step == 0 || step > remaining.len() {
        remaining
    } else {
        simulate(remove_at_index(remaining, (step - 1) as nat), (step + 1) as nat)
    }
}

spec fn final_list(n: nat) -> Seq<int>
{
    simulate(initial_list(n), 1)
}

spec fn even_list(k: nat) -> Seq<int>
    decreases k
{
    if k == 0 {
        Seq::empty()
    } else {
        even_list((k - 1) as nat).push((2 * k) as int)
    }
}

spec fn range_seq_measure(a: int, b: int) -> nat {
    if b >= a { (b - a + 1) as nat } else { 0 }
}

spec fn range_seq(a: int, b: int) -> Seq<int>
    decreases range_seq_measure(a, b)
{
    if a > b {
        Seq::empty()
    } else {
        seq![a] + range_seq(a + 1, b)
    }
}

proof fn even_list_length(k: nat)
    ensures even_list(k).len() == k
    decreases k
{
}

proof fn even_list_element(k: nat, i: nat)
    requires i < k
    ensures even_list(k).len() == k
    ensures even_list(k)[i as int] == 2 * (i as int + 1)
    decreases k
{
}

proof fn range_seq_length(a: int, b: int)
    ensures range_seq(a, b).len() == range_seq_measure(a, b)
    decreases range_seq_measure(a, b)
{
}

proof fn range_seq_append(a: int, b: int)
    requires a <= b
    ensures range_seq(a, b) == range_seq(a, b - 1).push(b)
    decreases (b - a) as nat
{
}

proof fn initial_list_equals_range(n: nat)
    ensures initial_list(n) == range_seq(1, n as int)
    decreases n
{
}

proof fn simulate_from_state(k: nat, n: nat)
    requires 2 * k <= n
    ensures simulate(
        even_list(k) + range_seq((2 * k) as int + 1, n as int),
        (k + 1) as nat,
    ) == even_list((n / 2) as nat)
    decreases n - 2 * k
{
}

proof fn final_list_is_even(n: nat)
    ensures final_list(n) == even_list((n / 2) as nat)
{
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
        final_list_is_even(n as nat);
        even_list_length((n / 2) as nat);
        even_list_element((n / 2) as nat, (x - 1) as nat);
    }
    2 * x
}

fn main() {}

} // verus!
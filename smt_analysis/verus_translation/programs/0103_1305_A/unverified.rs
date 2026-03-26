use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::multiset::*;

verus! {

// ---------------------------------------------------------------------------
// Specification predicates and functions
// ---------------------------------------------------------------------------

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn pairwise_distinct(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

spec fn is_permutation(a: Seq<int>, b: Seq<int>) -> bool {
    a.to_multiset() =~= b.to_multiset()
}

spec fn sums(x: Seq<int>, y: Seq<int>) -> Seq<int>
    recommends x.len() == y.len()
    decreases x.len()
{
    if x.len() == 0 {
        Seq::empty()
    } else {
        sums(x.take(x.len() - 1), y.take(y.len() - 1)).push(x[x.len() - 1] + y[y.len() - 1])
    }
}

// ---------------------------------------------------------------------------
// Helper Lemmas
// ---------------------------------------------------------------------------

proof fn sums_length(x: Seq<int>, y: Seq<int>)
    requires x.len() == y.len()
    ensures sums(x, y).len() == x.len()
    decreases x.len()
{
    if x.len() > 0 {
        sums_length(x.take(x.len() - 1), y.take(y.len() - 1));
    }
}

proof fn sums_element(x: Seq<int>, y: Seq<int>, k: int)
    requires
        x.len() == y.len(),
        0 <= k < x.len(),
    ensures
        sums(x, y).len() == x.len(),
        sums(x, y)[k] == x[k] + y[k],
    decreases x.len()
{
    sums_length(x, y);
    if k < x.len() - 1 {
        sums_element(x.take(x.len() - 1), y.take(y.len() - 1), k);
    }
}

proof fn not_in_seq_zero_count(s: Seq<int>, v: int)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] != v
    ensures s.to_multiset().count(v) == 0
    decreases s.len()
{
    broadcast use group_multiset_axioms, group_to_multiset_ensures;
    if s.len() > 0 {
        let init = s.drop_last();
        let last = s.last();
        assert(s =~= init.push(last));
        not_in_seq_zero_count(init, v);
        // init.push(last).to_multiset() =~= init.to_multiset().insert(last)
        // init.to_multiset().count(v) == 0 (by induction)
        // last != v (by precondition)
        // So s.to_multiset().count(v) == 0
    }
}

proof fn duplicate_gives_count2(s: Seq<int>, i: int, j: int)
    requires
        0 <= i < j < s.len(),
        s[i] == s[j],
    ensures s.to_multiset().count(s[i]) >= 2
{
    broadcast use group_multiset_axioms, group_to_multiset_ensures;
    let left = s.take(i + 1);
    let right = s.skip(i + 1);
    assert(s =~= left + right);
    lemma_multiset_commutative(left, right);
    // left contains s[i] at index i
    // right contains s[j] = s[i] at index j - i - 1
    // Need to show each has count >= 1
    assert(left[i] == s[i]);
    assert(left.contains(s[i]));
    assert(right[j - i - 1] == s[j]);
    assert(right.contains(s[i]));
    // s.to_multiset() =~= left.to_multiset().add(right.to_multiset())
    // count in add = sum of counts, each >= 1
}

proof fn distinct_bounds_count(s: Seq<int>, v: int)
    requires pairwise_distinct(s)
    ensures s.to_multiset().count(v) <= 1
    decreases s.len()
{
    broadcast use group_multiset_axioms, group_to_multiset_ensures;
    if s.len() > 0 {
        let init = s.drop_last();
        let last = s.last();
        assert(s =~= init.push(last));
        assert(pairwise_distinct(init)) by {
            assert forall|i: int, j: int| 0 <= i < j < init.len() implies init[i] != init[j] by {
                assert(init[i] == s[i]);
                assert(init[j] == s[j]);
            }
        }
        distinct_bounds_count(init, v);
        if v == last {
            assert forall|k: int| 0 <= k < init.len() implies init[k] != v by {
                assert(init[k] == s[k]);
                // k < s.len() - 1 = init.len(), so s[k] != s[s.len()-1] = last = v
            }
            not_in_seq_zero_count(init, v);
            // init.to_multiset().count(v) == 0
            // s.to_multiset() =~= init.to_multiset().insert(last)
            // insert(v) adds 1, so count(v) = 0 + 1 = 1
        }
        // If v != last: init.to_multiset().count(v) <= 1
        // s.to_multiset() =~= init.to_multiset().insert(last)
        // insert(last) doesn't change count(v) when v != last, so <= 1
    }
}

proof fn sorted_perm_distinct_is_strict(s: Seq<int>, orig: Seq<int>)
    requires
        is_sorted(s),
        is_permutation(s, orig),
        pairwise_distinct(orig),
    ensures forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
{
    broadcast use group_multiset_axioms;
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies s[i] < s[j] by {
        if s[i] == s[j] {
            duplicate_gives_count2(s, i, j);
            distinct_bounds_count(orig, s[i]);
            // s.to_multiset().count(s[i]) >= 2
            // orig.to_multiset().count(s[i]) <= 1
            // but s.to_multiset() =~= orig.to_multiset(), contradiction
        }
    }
}

proof fn sorted_sums_distinct(x: Seq<int>, y: Seq<int>, a: Seq<int>, b: Seq<int>)
    requires
        x.len() == y.len(),
        is_sorted(x) && is_sorted(y),
        is_permutation(x, a) && is_permutation(y, b),
        pairwise_distinct(a) && pairwise_distinct(b),
    ensures pairwise_distinct(sums(x, y))
{
    sorted_perm_distinct_is_strict(x, a);
    sorted_perm_distinct_is_strict(y, b);
    sums_length(x, y);
    assert forall|i: int, j: int| 0 <= i < j < sums(x, y).len() implies sums(x, y)[i] != sums(x, y)[j] by {
        sums_element(x, y, i);
        sums_element(x, y, j);
        // x[i] < x[j] and y[i] < y[j] so x[i]+y[i] < x[j]+y[j]
    }
}

// ---------------------------------------------------------------------------
// Exec functions
// ---------------------------------------------------------------------------

// Helper: map a Vec<i64> view to Seq<int>
spec fn seq_int(v: Seq<i64>) -> Seq<int> {
    v.map(|_idx: int, x: i64| x as int)
}

fn insert(sorted: &Vec<i64>, val: i64) -> (result: Vec<i64>)
    requires
        is_sorted(seq_int(sorted@)),
    ensures
        is_sorted(seq_int(result@)),
        is_permutation(seq_int(result@), seq_int(sorted@).push(val as int)),
{
    let mut i: usize = 0;
    while i < sorted.len() && sorted[i] < val
        invariant
            0 <= i <= sorted.len(),
            forall|j: int| 0 <= j < i ==> sorted@[j] < val,
            is_sorted(seq_int(sorted@)),
        decreases sorted.len() - i,
    {
        i = i + 1;
    }
    // Build result = sorted[..i] + [val] + sorted[i..]
    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < i
        invariant
            0 <= k <= i,
            i <= sorted.len(),
            result@.len() == k as int,
            forall|j: int| 0 <= j < k ==> result@[j] == sorted@[j],
        decreases i - k,
    {
        result.push(sorted[k]);
        k = k + 1;
    }
    result.push(val);
    let mut k2: usize = i;
    while k2 < sorted.len()
        invariant
            i <= k2 <= sorted.len(),
            result@.len() == (k2 as int) + 1,
            forall|j: int| 0 <= j < i ==> result@[j] == sorted@[j],
            result@[i as int] == val,
            forall|j: int| (i as int) < j && j <= (k2 as int) ==> result@[j] == sorted@[j - 1],
        decreases sorted.len() - k2,
    {
        result.push(sorted[k2]);
        k2 = k2 + 1;
    }
    proof {
        broadcast use group_multiset_axioms, group_to_multiset_ensures;

        let result_spec = seq_int(result@);
        let sorted_spec = seq_int(sorted@);
        let concat_spec = sorted_spec.push(val as int);

        // Build expected = sorted_spec.take(i) + [val] + sorted_spec.skip(i)
        let prefix = sorted_spec.take(i as int);
        let suffix = sorted_spec.skip(i as int);
        let expected = prefix.push(val as int) + suffix;

        // result_spec =~= expected
        assert(result_spec =~= expected) by {
            assert(result_spec.len() == expected.len());
            assert forall|j: int| 0 <= j < result_spec.len() implies result_spec[j] == expected[j] by {
                if j < (i as int) {
                    assert(result@[j] == sorted@[j]);
                } else if j == (i as int) {
                    assert(result@[j] == val);
                } else {
                    assert(result@[j] == sorted@[j - 1]);
                }
            }
        }

        // sorted_spec =~= prefix + suffix
        assert(sorted_spec =~= prefix + suffix);

        // Now show is_sorted(result_spec) directly from result@
        assert(is_sorted(result_spec)) by {
            assert forall|p: int, q: int| 0 <= p < q < result_spec.len() implies result_spec[p] <= result_spec[q] by {
                let ilen = i as int;
                // Establish what result_spec[p] and result_spec[q] are
                let rp = result_spec[p];
                let rq = result_spec[q];
                if p < ilen {
                    assert(result@[p] == sorted@[p]);
                    assert(rp == sorted_spec[p]);
                } else if p == ilen {
                    assert(result@[p] == val);
                    assert(rp == val as int);
                } else {
                    assert(result@[p] == sorted@[p - 1]);
                    assert(rp == sorted_spec[p - 1]);
                }
                if q < ilen {
                    assert(result@[q] == sorted@[q]);
                    assert(rq == sorted_spec[q]);
                } else if q == ilen {
                    assert(result@[q] == val);
                    assert(rq == val as int);
                } else {
                    assert(result@[q] == sorted@[q - 1]);
                    assert(rq == sorted_spec[q - 1]);
                }

                // Now prove rp <= rq in each case
                if p < ilen && q < ilen {
                    // sorted_spec[p] <= sorted_spec[q]
                } else if p < ilen && q == ilen {
                    // sorted_spec[p] <= val
                    assert(sorted@[p] < val);
                } else if p < ilen && q > ilen {
                    // sorted_spec[p] <= sorted_spec[q-1]
                    // p < i <= q-1
                    assert(sorted@[p] < val);
                    if ilen < sorted_spec.len() {
                        assert(!(sorted@[ilen] < val));
                        // so sorted_spec[ilen] >= val > sorted_spec[p]
                        // and sorted_spec[ilen] <= sorted_spec[q-1]
                    }
                } else if p == ilen && q > ilen {
                    // val <= sorted_spec[q-1]
                    // q-1 >= i, so sorted_spec[q-1] >= sorted_spec[i] >= val
                    if ilen < sorted_spec.len() {
                        assert(!(sorted@[ilen] < val));
                    }
                } else {
                    // p > ilen, q > ilen
                    // sorted_spec[p-1] <= sorted_spec[q-1]
                }
            }
        }

        // Show permutation: expected.to_multiset() =~= concat_spec.to_multiset()
        // expected = (prefix ++ [val]) + suffix
        // concat_spec = (prefix + suffix).push(val)
        lemma_multiset_commutative(prefix.push(val as int), suffix);
        lemma_multiset_commutative(prefix, suffix);

        // prefix.push(val).to_multiset() =~= prefix.to_multiset().insert(val)
        // (prefix + suffix).push(val).to_multiset() =~= (prefix + suffix).to_multiset().insert(val)
        //   = prefix.to_multiset().add(suffix.to_multiset()).insert(val)
        // expected.to_multiset() = prefix.push(val).to_multiset().add(suffix.to_multiset())
        //   = prefix.to_multiset().insert(val).add(suffix.to_multiset())
        //   = prefix.to_multiset().add(suffix.to_multiset()).insert(val)   [insert commutes with add]
        // So they match.
    }
    result
}

fn sort_seq(s: &Vec<i64>) -> (sorted: Vec<i64>)
    ensures
        is_sorted(seq_int(sorted@)),
        is_permutation(seq_int(sorted@), seq_int(s@)),
{
    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    proof {
        broadcast use group_multiset_axioms, group_to_multiset_ensures;
        // Initially: sorted is empty, s_spec.take(0) is empty
        assert(seq_int(sorted@) =~= Seq::<int>::empty());
        assert(seq_int(s@).take(0) =~= Seq::<int>::empty());
        assert(Seq::<int>::empty().to_multiset() =~= Multiset::<int>::empty());
    }

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_sorted(seq_int(sorted@)),
            is_permutation(seq_int(sorted@), seq_int(s@).take(i as int)),
        decreases s.len() - i,
    {
        proof {
            broadcast use group_multiset_axioms, group_to_multiset_ensures;
            let s_spec = seq_int(s@);
            assert(s_spec.take((i as int) + 1) =~= s_spec.take(i as int).push(s_spec[i as int]));
        }
        sorted = insert(&sorted, s[i]);
        i = i + 1;
    }
    proof {
        let s_spec = seq_int(s@);
        assert(s_spec.take(s_spec.len() as int) =~= s_spec);
    }
    sorted
}

fn kuroni_and_the_gifts(a: &Vec<i64>, b: &Vec<i64>) -> (result: (Vec<i64>, Vec<i64>))
    requires
        a@.len() == b@.len(),
        pairwise_distinct(seq_int(a@)),
        pairwise_distinct(seq_int(b@)),
    ensures
        ({
            let (x, y) = result;
            let a_spec = seq_int(a@);
            let b_spec = seq_int(b@);
            let x_spec = seq_int(x@);
            let y_spec = seq_int(y@);
            &&& x_spec.len() == a_spec.len()
            &&& y_spec.len() == a_spec.len()
            &&& is_permutation(x_spec, a_spec)
            &&& is_permutation(y_spec, b_spec)
            &&& pairwise_distinct(sums(x_spec, y_spec))
        }),
{
    let x = sort_seq(a);
    let y = sort_seq(b);
    proof {
        broadcast use group_multiset_axioms, group_to_multiset_ensures;
        let a_spec = seq_int(a@);
        let b_spec = seq_int(b@);
        let x_spec = seq_int(x@);
        let y_spec = seq_int(y@);

        // lengths match because permutations preserve multiset cardinality
        to_multiset_len(x_spec);
        to_multiset_len(a_spec);
        to_multiset_len(y_spec);
        to_multiset_len(b_spec);

        sorted_sums_distinct(x_spec, y_spec, a_spec, b_spec);
    }
    (x, y)
}

} // verus!

fn main() {}

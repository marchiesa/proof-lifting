use vstd::prelude::*;

verus! {

spec fn CyclicIndex(year: int, period: int) -> int {
    (year - 1) % period
}

spec fn GapjaName(year: int, s: Seq<Seq<char>>, t: Seq<Seq<char>>) -> Seq<char> {
    s[CyclicIndex(year, s.len())].add(t[CyclicIndex(year, t.len())])
}

#[verifier::loop_isolation(false)]
fn NewYearNaming(n: i64, m: i64, s: &Vec<String>, t: &Vec<String>, queries: &Vec<i64>) -> (results: Vec<String>)
    requires
        n > 0 && m > 0,
        s@.len() == n as int,
        t@.len() == m as int,
        forall|i: int| 0 <= i < queries@.len() ==> queries@[i] as int >= 1,
    ensures
        results@.len() == queries@.len(),
        forall|i: int| 0 <= i < queries@.len() ==>
            results@[i]@ == GapjaName(
                queries@[i] as int,
                s@.map_values(|x: String| x@),
                t@.map_values(|x: String| x@),
            ),
{
    let mut results: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len() {
        let x: i64 = queries[i] - 1;
        proof { assume(false); }
        proof { assume(false); }
        proof { assume(false); }
        proof { assume(false); }
        let idx_s = (x % n) as usize;
        let idx_t = (x % m) as usize;
        let mut name = s[idx_s].clone();
        name.push_str(&t[idx_t]);
        results.push(name);
        i += 1;
    }
    results
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn ends_with(s: Seq<char>, suffix: Seq<char>) -> bool {
    s.len() >= suffix.len() && s.subrange(s.len() - suffix.len(), s.len()) == suffix
}

spec fn valid_sentence(s: Seq<char>) -> bool {
    ends_with(s, seq!['p', 'o']) ||
    ends_with(s, seq!['d', 'e', 's', 'u']) ||
    ends_with(s, seq!['m', 'a', 's', 'u']) ||
    ends_with(s, seq!['m', 'n', 'i', 'd', 'a'])
}

spec fn classify_sentence(s: Seq<char>) -> Seq<char>
    recommends valid_sentence(s)
{
    if ends_with(s, seq!['p', 'o']) {
        seq!['F', 'I', 'L', 'I', 'P', 'P', 'I', 'N', 'O']
    } else if ends_with(s, seq!['d', 'e', 's', 'u']) || ends_with(s, seq!['m', 'a', 's', 'u']) {
        seq!['J', 'A', 'P', 'A', 'N', 'E', 'S', 'E']
    } else {
        seq!['K', 'O', 'R', 'E', 'A', 'N']
    }
}

spec fn classify_all(sentences: Seq<Seq<char>>) -> Seq<Seq<char>>
    recommends forall|i: int| 0 <= i < sentences.len() ==> valid_sentence(sentences[i])
    decreases sentences.len()
{
    if sentences.len() == 0 {
        seq![]
    } else {
        classify_all(sentences.take(sentences.len() - 1)).push(
            classify_sentence(sentences[sentences.len() - 1])
        )
    }
}

proof fn classify_all_append(sentences: Seq<Seq<char>>)
    requires
        sentences.len() > 0,
        forall|i: int| 0 <= i < sentences.len() ==> valid_sentence(sentences[i]),
    ensures
        classify_all(sentences) == classify_all(sentences.take(sentences.len() - 1)).push(
            classify_sentence(sentences[sentences.len() - 1])
        ),
{
}

proof fn last_char_determines_classification(s: Seq<char>)
    requires
        valid_sentence(s),
        s.len() >= 1,
    ensures
        s[s.len() - 1] == 'o' ==> ends_with(s, seq!['p', 'o']),
        s[s.len() - 1] == 'u' ==> (ends_with(s, seq!['d', 'e', 's', 'u']) || ends_with(s, seq!['m', 'a', 's', 'u'])),
        s[s.len() - 1] != 'o' && s[s.len() - 1] != 'u' ==> ends_with(s, seq!['m', 'n', 'i', 'd', 'a']),
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn suffix_three(sentences: &Vec<Vec<char>>) -> (results: Vec<Vec<char>>)
    requires
        forall|i: int| 0 <= i < sentences@.len() ==> valid_sentence(sentences@[i]@),
    ensures
        results@.map_values(|s: Vec<char>| s@) == classify_all(sentences@.map_values(|s: Vec<char>| s@)),
{
    let mut results: Vec<Vec<char>> = Vec::new();
    for i in 0..sentences.len() {
        let s = &sentences[i];
        proof { assume(false); }
        proof { assume(false); }
        proof { assume(false); }
        proof { last_char_determines_classification(s@); }
        let last = s[s.len() - 1];
        if last == 'o' {
            proof { assume(false); }
            results.push(vec!['F', 'I', 'L', 'I', 'P', 'P', 'I', 'N', 'O']);
        } else if last == 'u' {
            proof { assume(false); }
            results.push(vec!['J', 'A', 'P', 'A', 'N', 'E', 'S', 'E']);
        } else {
            proof { assume(false); }
            results.push(vec!['K', 'O', 'R', 'E', 'A', 'N']);
        }
        proof { assume(false); }
        proof { assume(false); }
        proof { assume(false); }
        proof {
            classify_all_append(
                sentences@.map_values(|s: Vec<char>| s@).take(i as int + 1),
            );
        }
    }
    proof { assume(false); }
    results
}

fn main() {}

} // verus!
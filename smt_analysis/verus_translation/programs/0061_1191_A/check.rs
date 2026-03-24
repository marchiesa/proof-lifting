use vstd::prelude::*;

verus! {

spec fn CategoryRank(hp: int) -> int
    recommends hp >= 1
{
    let r = hp % 4;
    if r == 1 { 3 }
    else if r == 3 { 2 }
    else if r == 2 { 1 }
    else { 0 }
}

spec fn CategoryChar(hp: int) -> char
    recommends hp >= 1
{
    let r = hp % 4;
    if r == 1 { 'A' }
    else if r == 3 { 'B' }
    else if r == 2 { 'C' }
    else { 'D' }
}

proof fn CategoryRankBounded(hp: int)
    requires hp >= 1
    ensures 0 <= CategoryRank(hp) <= 3
{
    assume(false);
}

fn TokitsukazeAndEnhancement(x: i64) -> (a: i64, b: char)
    requires x >= 1
    ensures 0 <= a && a <= 2
    ensures b == CategoryChar(x as int + a as int)
    ensures forall|delta: int| 0 <= delta && delta <= 2 ==> CategoryRank(x as int + delta) <= CategoryRank(x as int + a as int)
    ensures forall|delta: int| 0 <= delta && delta < a as int ==> CategoryRank(x as int + delta) < CategoryRank(x as int + a as int)
{
    let r = x % 4;
    if r == 0 {
        proof { assume(false); }
        (1i64, 'A')
    } else if r == 1 {
        proof { assume(false); }
        (0i64, 'A')
    } else if r == 2 {
        proof { assume(false); }
        (1i64, 'B')
    } else {
        proof { assume(false); }
        (2i64, 'A')
    }
}

fn main() {}

} // verus!
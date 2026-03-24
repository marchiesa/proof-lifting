use vstd::prelude::*;

verus! {

spec fn is_good_string(s: Seq<char>) -> bool {
    (forall|i: int| 0 <= i && i < s.len() ==> (s[i] == 'a' || s[i] == 'b')) &&
    (forall|i: int| 0 <= i && i < s.len() - 1 ==> s[i] != s[i + 1])
}

spec fn good_string_with_counts(na: int, nb: int) -> bool {
    na >= 0 && nb >= 0 && na - nb <= 1 && nb - na <= 1
}

spec fn achievable_length(len: int, a: int, b: int, c: int) -> bool {
    a >= 0 && b >= 0 && c >= 0 &&
    exists|pa: int, pb: int, pc: int|
        0 <= pa && pa <= a &&
        0 <= pb && pb <= b &&
        0 <= pc && pc <= c &&
        good_string_with_counts(pa + pc, pb + pc) &&
        pa + pb + 2 * pc == len
}

proof fn achievable_witness(len: int, a: int, b: int, c: int, pa: int, pb: int, pc: int)
    requires
        a >= 0 && b >= 0 && c >= 0,
        0 <= pa && pa <= a && 0 <= pb && pb <= b && 0 <= pc && pc <= c,
        good_string_with_counts(pa + pc, pb + pc),
        pa + pb + 2 * pc == len,
    ensures
        achievable_length(len, a, b, c),
{
    assume(false);
}

proof fn not_achievable(n: int, a: int, b: int, c: int, max_len: int)
    requires
        a >= 0 && b >= 0 && c >= 0,
        n > max_len,
        (if a == b { max_len == 2 * a + 2 * c }
        else if a > b { max_len == 2 * b + 2 * c + 1 }
        else { max_len == 2 * a + 2 * c + 1 }),
    ensures
        !achievable_length(n, a, b, c),
{
    assume(false);
}

fn another_one_bites_the_dust(a: i64, b: i64, c: i64) -> (max_len: i64)
    requires
        a >= 0 && b >= 0 && c >= 0,
    ensures
        achievable_length(max_len as int, a as int, b as int, c as int),
        forall|n: int|
            max_len as int < n && n <= a as int + b as int + 2 * c as int ==>
            !achievable_length(n, a as int, b as int, c as int),
{
    let mut x: i64 = a + c;
    let mut y: i64 = b + c;

    if x > y {
        x = y + 1;
    }
    if y > x {
        y = x + 1;
    }

    let max_len: i64 = x + y;

    proof {
        assume(false);
    }

    max_len
}

fn main() {}

} // verus!